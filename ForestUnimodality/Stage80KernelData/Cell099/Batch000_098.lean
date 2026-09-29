import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell099.Parameters
import ForestUnimodality.BinomialMassData.Q53_103.Batch000_049
import ForestUnimodality.BinomialMassData.Q53_103.Batch050_099
import ForestUnimodality.BinomialMassData.Q21967_42642.Batch000_049
import ForestUnimodality.BinomialMassData.Q21967_42642.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree000.table
  base := (3887924227571177520189849101/100000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1259755093603685816017190300000000000000)
      linear := (-52077850725735326184451246000000000000)
      constant := (388792422757117752018984910100000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree000.table
  base := (3887924227571177520189849101/100000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1259755093603685816017190300000000000000)
      linear := (-52077850725735326184451246000000000000)
      constant := (388792422757117752018984910100000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree001.table
  base := (44116373786560174016576826979451402119609/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-14306500030314367814766526964214000000000000)
      constant := (2343975992553128973312150994029613625434659405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree001.table
  base := (110195687783607541729864553632320639814289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-613690700757708451127013476749263186000000000000)
      constant := (100350791466067203645387394758564375686249594901698) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24988522174567113069/50000000000000000000)
  directionHi := (49977044349134226139/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree002.table
  base := (129877362677811413107906498922722727364641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-28060506142279409554042210659614000000000000)
      constant := (1392592134854855873781831035985793414611476369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree002.table
  base := (3241824626543355247463028588467605063963/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-1203707589608066629245319810273115286000000000000)
      constant := (59579684002868290846658531636259096828937119099320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24988522174567113069/50000000000000000000)
  centralHi := (49977044349134226139/100000000000000000000)
  directionLo := (17669553481466818341/25000000000000000000)
  directionHi := (14135642785173454673/20000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree003.table
  base := (15981638266332907838910756609225597604353/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-41814512254244451293317894355014000000000000)
      constant := (880446749320359244866674430366413824922904885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree003.table
  base := (39870354572147530337048582209169944886729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3939737022)
      previous := (1969868511)
      next := (1969868511)
      square := (63629535652865594936143656581144700000000000000)
      linear := (-199302719828713867484847349310774154000000000000)
      constant := (4183697883143978619339774706424866689178098404642) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17669553481466818341/25000000000000000000)
  centralHi := (14135642785173454673/20000000000000000000)
  directionLo := (86562780024823531863/100000000000000000000)
  directionHi := (10820347503102941483/12500000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree004.table
  base := (51508248697872507053355616341797238595483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-55568518366209493032593578050414000000000000)
      constant := (604206615311100639226690012020982904259479147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree004.table
  base := (51382982024989223523859518775245100686227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-2383741367308782985481932477320819486000000000000)
      constant := (25838291880070040852947860918595060924497628930307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86562780024823531863/100000000000000000000)
  centralHi := (10820347503102941483/12500000000000000000)
  directionLo := (99954088698268452277/100000000000000000000)
  directionHi := (49977044349134226139/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree005.table
  base := (34661859130397713991745297434346470111311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-69322524478174534771869261745814000000000000)
      constant := (457615429898267129896437646058051701410898399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree005.table
  base := (34570759456739800800247811503760631413327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-2973758256159141163600238810844671586000000000000)
      constant := (19575663307942725036059151559490590465213142241407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99954088698268452277/100000000000000000000)
  centralHi := (49977044349134226139/50000000000000000000)
  directionLo := (55876034239592931283/50000000000000000000)
  directionHi := (111752068479185862567/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree006.table
  base := (602794803277552094412465388962465498747/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-83076530590139576511144945441214000000000000)
      constant := (384899234727111866117641680468795859048276920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree006.table
  base := (24045135946823508067647793512629812494697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3939737022)
      previous := (1969868511)
      next := (1969868511)
      square := (63629535652865594936143656581144700000000000000)
      linear := (-395975016112166593524282793818724854000000000000)
      constant := (1830530606987680074063719888575251444080460891953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55876034239592931283/50000000000000000000)
  centralHi := (111752068479185862567/100000000000000000000)
  directionLo := (24483651501564856011/20000000000000000000)
  directionHi := (15302282188478035007/12500000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree007.table
  base := (17083389499208515114823761578915281328637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-96830536702104618250420629136614000000000000)
      constant := (356621680945590580275073812136410219615509933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree007.table
  base := (17033287948086660584511676283169345546593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-4153792033859857519836851477892375786000000000000)
      constant := (15275144239040604532953267384430102057241146315313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24483651501564856011/20000000000000000000)
  centralHi := (15302282188478035007/12500000000000000000)
  directionLo := (2066044228278985427/1562500000000000000)
  directionHi := (132226830609855067329/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree008.table
  base := (3024600720564856795036777461022387135841/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-110584542814069659989696312832014000000000000)
      constant := (357100031782480797379614446524058020496548676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree008.table
  base := (12059303607866200758904397898247280167611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-4743808922710215697955157811416227886000000000000)
      constant := (15305842186341954640583355330312141371131933307051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2066044228278985427/1562500000000000000)
  centralHi := (132226830609855067329/100000000000000000000)
  directionLo := (17669553481466818341/12500000000000000000)
  directionHi := (141356427851734546729/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree009.table
  base := (83582293680303267937192109462602048549/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-124338548926034701728971996527414000000000000)
      constant := (377861908941992869297910674864800513305634100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree009.table
  base := (8326497426859651972904353848167061254887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (437748558)
      previous := (218874279)
      next := (218874279)
      square := (7069948405873954992904850731238300000000000000)
      linear := (-65849701377291035507079804258519506000000000000)
      constant := (200058123388008014625979122395027006659287880807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17669553481466818341/12500000000000000000)
  centralHi := (141356427851734546729/100000000000000000000)
  directionLo := (9370695815462667401/6250000000000000000)
  directionHi := (149931133047402678417/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree010.table
  base := (5422475528661073276543531434985544375067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-138092555037999743468247680222814000000000000)
      constant := (414235178547958563566488273782901640275085803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree010.table
  base := (5395826932650075903222759744190365361609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-5923842700410932054191770478463932086000000000000)
      constant := (17772159522976292888529424829290469859712007090969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9370695815462667401/6250000000000000000)
  centralHi := (149931133047402678417/100000000000000000000)
  directionLo := (158041290866511505003/100000000000000000000)
  directionHi := (39510322716627876251/25000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree011.table
  base := (1520526544168818270534699866495880093841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-151846561149964785207523363918214000000000000)
      constant := (463566654082266834986522168515063583831118338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree011.table
  base := (3018082516013003779269221551924066287459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-6513859589261290232310076811987784186000000000000)
      constant := (19894909811557986637776649209861233648171267300819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158041290866511505003/100000000000000000000)
  centralHi := (39510322716627876251/25000000000000000000)
  directionLo := (16575510423702982347/10000000000000000000)
  directionHi := (165755104237029823471/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree012.table
  base := (133275687358597550036690183511932200277/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-165600567261929826946799047613614000000000000)
      constant := (524288786325156858850094409066792709701909544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree012.table
  base := (523025417070168797562215349756677519899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3939737022)
      previous := (1969868511)
      next := (1969868511)
      square := (63629535652865594936143656581144700000000000000)
      linear := (-789319608679072045603153682834626254000000000000)
      constant := (2500670875188618238365903880653467679201570051302) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16575510423702982347/10000000000000000000)
  centralHi := (165755104237029823471/100000000000000000000)
  directionLo := (86562780024823531863/50000000000000000000)
  directionHi := (173125560049647063727/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree013.table
  base := (-29689832213458196986998676024401332891/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-179354573373894868686074731309014000000000000)
      constant := (595428418024037032922127168902324525187187620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree013.table
  base := (-611673576081404869025268114237269302523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-7693893366962006588546689479035488386000000000000)
      constant := (25563992162197959108532120469896572118384540641557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86562780024823531863/50000000000000000000)
  centralHi := (173125560049647063727/100000000000000000000)
  directionLo := (180194795996941267681/100000000000000000000)
  directionHi := (90097397998470633841/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree014.table
  base := (-1999197072759801603190562514178255158631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-193108579485859910425350415004414000000000000)
      constant := (676346423429475990440412553543078891022083721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree014.table
  base := (-2015146387436302191451167779812864657473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-8283910255812364766664995812559340486000000000000)
      constant := (29041472257584338582842928454163164101355185338607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180194795996941267681/100000000000000000000)
  centralHi := (90097397998470633841/50000000000000000000)
  directionLo := (186996977158066942889/100000000000000000000)
  directionHi := (18699697715806694289/10000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree015.table
  base := (-638379610215212815046521491637465948287/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-206862585597824952164626098699814000000000000)
      constant := (766598261417680401278735757112300618773116085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree015.table
  base := (-3206162747246526875536349358993931970267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3939737022)
      previous := (1969868511)
      next := (1969868511)
      square := (63629535652865594936143656581144700000000000000)
      linear := (-985991904962524771642589127342576954000000000000)
      constant := (3657719857121961304507343148389463611838329447117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186996977158066942889/100000000000000000000)
  centralHi := (18699697715806694289/10000000000000000000)
  directionLo := (12097516278554146889/6250000000000000000)
  directionHi := (7742410418274654009/4000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree016.table
  base := (-840522407159219759018516896472802820409/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-220616591709789993903901782395214000000000000)
      constant := (865858103536812699254343094348424174391404595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree016.table
  base := (-4215374624150350372336274711159622488401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-9463944033513081122901608479607044686000000000000)
      constant := (37184077605317739239954423491302789629565709390559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12097516278554146889/6250000000000000000)
  centralHi := (7742410418274654009/4000000000000000000)
  directionLo := (39981635479307380911/20000000000000000000)
  directionHi := (49977044349134226139/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree017.table
  base := (-5054843550819093901686065561123705654269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-234370597821755035643177466090614000000000000)
      constant := (973876590292826397401479262174876606713860179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree017.table
  base := (-202650083008752066565665313824572652417/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-10053960922363439301019914813130896786000000000000)
      constant := (41824599794388695031181132784343134461838482647575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39981635479307380911/20000000000000000000)
  centralHi := (49977044349134226139/25000000000000000000)
  directionLo := (51515158176914660091/25000000000000000000)
  directionHi := (41212126541531728073/20000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree018.table
  base := (-1441794765499995078123253265176018552481/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-248124603933720077382453149786014000000000000)
      constant := (1090456537869466533616599339848242476706916284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree018.table
  base := (-180542535640739113302537564868074910941/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (437748558)
      previous := (218874279)
      next := (218874279)
      square := (7069948405873954992904850731238300000000000000)
      linear := (-131407133471775277520224952427836406000000000000)
      constant := (578180314039905891469568255075803592871630287968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51515158176914660091/25000000000000000000)
  centralHi := (41212126541531728073/20000000000000000000)
  directionLo := (212034641777601820093/100000000000000000000)
  directionHi := (106017320888800910047/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree019.table
  base := (-6354661207498778030640236148035446709427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-261878610045685119121728833481414000000000000)
      constant := (1215438358918493455686531008916557945859688957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree019.table
  base := (-6363731322786185122823512410443132243893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-11233994700064155657256527480178600986000000000000)
      constant := (52201262346710745778732585907037550734741478595387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212034641777601820093/100000000000000000000)
  centralHi := (106017320888800910047/50000000000000000000)
  directionLo := (10892244290736328369/5000000000000000000)
  directionHi := (217844885814726567381/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree020.table
  base := (-6829657376405571318133712532544668855617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-275632616157650160861004517176814000000000000)
      constant := (1348690847809050459675652851860513608110759247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree020.table
  base := (-683772049032896577608836668452323168141/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-11824011588914513835374833813702453086000000000000)
      constant := (57924952820772990658074701509013893880653736212190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10892244290736328369/5000000000000000000)
  centralHi := (217844885814726567381/100000000000000000000)
  directionLo := (223504136958371725133/100000000000000000000)
  directionHi := (111752068479185862567/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree021.table
  base := (-3601220433221795037554232109646789915519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-289386622269615202600280200872214000000000000)
      constant := (1490105015125591799573432420228408411572517858) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree021.table
  base := (-1802398529325497219802974762826769540453/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3939737022)
      previous := (1969868511)
      next := (1969868511)
      square := (63629535652865594936143656581144700000000000000)
      linear := (-1379336497529430223721460016358478354000000000000)
      constant := (7111001147602517788387614208868335636246943038412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223504136958371725133/100000000000000000000)
  centralHi := (111752068479185862567/50000000000000000000)
  directionLo := (229023588740072613047/100000000000000000000)
  directionHi := (28627948592509076631/12500000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree022.table
  base := (-7481602172578454060326394433359081964309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-303140628381580244339555884567614000000000000)
      constant := (1639589724307027215359164682705401499440645819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree022.table
  base := (-7487935632490229616805014615261372275241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-13004045366615230191611446480750157286000000000000)
      constant := (70419532971333615566493734153479826900543306730119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229023588740072613047/100000000000000000000)
  centralHi := (28627948592509076631/12500000000000000000)
  directionLo := (46882623288914729531/20000000000000000000)
  directionHi := (29301639555571705957/12500000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree023.table
  base := (-7674354859550475169704197784126934029569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-316894634493545286078831568263014000000000000)
      constant := (1797068446645026738129069426180519356880302479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree023.table
  base := (-153599037536164345308614128193564252403/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8593290000000000000000000000000000000000000000
      center := (67027662)
      previous := (33513831)
      next := (33513831)
      square := (1082544084831361728592236123308700000000000000)
      linear := (-25697660218271433591171555414506634000000000000)
      constant := (145904054116130898492265088474265613227339120650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46882623288914729531/20000000000000000000)
  centralHi := (29301639555571705957/12500000000000000000)
  directionLo := (119840742365787868937/50000000000000000000)
  directionHi := (1917451877852605903/800000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree024.table
  base := (-3893386137330897363434833539017304038329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-330648640605510327818107251958414000000000000)
      constant := (1962476749998061950580779396770266842914735278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree024.table
  base := (-7791709669994734082671070301715388951723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3939737022)
      previous := (1969868511)
      next := (1969868511)
      square := (63629535652865594936143656581144700000000000000)
      linear := (-1576008793812882949760895460866429054000000000000)
      constant := (9365265267913539484597665690821912645227783669373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119840742365787868937/50000000000000000000)
  centralHi := (1917451877852605903/800000000000000000)
  directionLo := (24483651501564856011/10000000000000000000)
  directionHi := (244836515015648560111/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree025.table
  base := (-3911988114314991174343298407820601398291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-344402646717475369557382935653814000000000000)
      constant := (2135760297076230156648986598618212479531061562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree025.table
  base := (-7828324473234357375992428462851760261363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-14774096033166304725966365481321713586000000000000)
      constant := (91729635910567120759523764726571013984666129929117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24483651501564856011/10000000000000000000)
  centralHi := (244836515015648560111/100000000000000000000)
  directionLo := (124942610872835565347/50000000000000000000)
  directionHi := (49977044349134226139/20000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree026.table
  base := (-779029052886740637222994924089387646703/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-358156652829440411296658619349214000000000000)
      constant := (2316873216606693540645662757278320864561278730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree026.table
  base := (-7794113956824990912014217540460846161489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-15364112922016662904084671814845565686000000000000)
      constant := (99508027377139644430879801290664715974784830313951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124942610872835565347/50000000000000000000)
  centralHi := (49977044349134226139/20000000000000000000)
  directionLo := (127416962183963718739/50000000000000000000)
  directionHi := (254833924367927437479/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree027.table
  base := (-153787353101711948842315600113109703567/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-371910658941405453035934303044614000000000000)
      constant := (2505776759432192473962076138339978957742884850) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree027.table
  base := (-192318118112521284865147499246699696617/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (437748558)
      previous := (218874279)
      next := (218874279)
      square := (7069948405873954992904850731238300000000000000)
      linear := (-196964565566259519533370100597153306000000000000)
      constant := (1328653137276930823728589092220592465357369626520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127416962183963718739/50000000000000000000)
  centralHi := (254833924367927437479/100000000000000000000)
  directionLo := (259688340074470595589/100000000000000000000)
  directionHi := (25968834007447059559/10000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree028.table
  base := (-7524294223949432524503904547860590899563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-385664665053370494775209986740014000000000000)
      constant := (2702438179636529276864237259822138991146536133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree028.table
  base := (-3763618911554619859364243720674584385657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-16544146699717379260321284481893269886000000000000)
      constant := (116066865539634974434856322071555247926776305686126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259688340074470595589/100000000000000000000)
  centralHi := (25968834007447059559/10000000000000000000)
  directionLo := (2066044228278985427/781250000000000000)
  directionHi := (264453661219710134657/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree029.table
  base := (-1459535860778236666786980316417097026747/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-399418671165335536514485670435414000000000000)
      constant := (2906829797612705978732585122141861088216205385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree029.table
  base := (-3650128545752778541659967400149289159997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-17134163588567737438439590815417121986000000000000)
      constant := (124844727971557537622310958735876824406163816390246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2066044228278985427/781250000000000000)
  centralHi := (264453661219710134657/100000000000000000000)
  directionLo := (269134620393557969457/100000000000000000000)
  directionHi := (134567310196778984729/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree030.table
  base := (-3505864320116137573922529222521481125291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-413172677277300578253761354130814000000000000)
      constant := (3118928212608607578798798152943959213483575562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree030.table
  base := (-876747925881967993186563023213680848893/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3939737022)
      previous := (1969868511)
      next := (1969868511)
      square := (63629535652865594936143656581144700000000000000)
      linear := (-1969353386379788401839766349882330454000000000000)
      constant := (14883721214363494918853298892975081538484498480344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269134620393557969457/100000000000000000000)
  centralHi := (134567310196778984729/50000000000000000000)
  directionLo := (273735545474569083329/100000000000000000000)
  directionHi := (27373554547456908333/10000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree031.table
  base := (-1333661436454693213855731707545184291239/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-426926683389265619993037037826214000000000000)
      constant := (3338713639377102334347679549627299699271227245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree031.table
  base := (-1334055444448024836481536969817880457417/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-18314197366268453794676203482464826186000000000000)
      constant := (143392308678909677795569781419234321814659971504515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273735545474569083329/100000000000000000000)
  centralHi := (27373554547456908333/10000000000000000000)
  directionLo := (278260406486685072263/100000000000000000000)
  directionHi := (34782550810835634033/12500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree032.table
  base := (-6268991831952583292651176974313622035551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-440680689501230661732312721521614000000000000)
      constant := (3566169348565531836673675536705554783824839441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree032.table
  base := (-1567677828210667810367961977884974163877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-18904214255118811972794509815988678286000000000000)
      constant := (153160466260127966823249096323505468857720132944172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278260406486685072263/100000000000000000000)
  centralHi := (34782550810835634033/12500000000000000000)
  directionLo := (282712855703469093457/100000000000000000000)
  directionHi := (141356427851734546729/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree033.table
  base := (-726889497919063175149387991412614052709/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-454434695613195703471588405217014000000000000)
      constant := (3801281194196070826887272625896290620118481752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree033.table
  base := (-5816615309157854222272252360239068113599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3939737022)
      previous := (1969868511)
      next := (1969868511)
      square := (63629535652865594936143656581144700000000000000)
      linear := (-2166025682663241127879201794390281154000000000000)
      constant := (18139706582542710586112058615536131393308645103049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282712855703469093457/100000000000000000000)
  centralHi := (141356427851734546729/50000000000000000000)
  directionLo := (17943516384525683757/6250000000000000000)
  directionHi := (287096262152410940113/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree034.table
  base := (-2653903575869557577718736322656445399427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-468188701725160745210864088912414000000000000)
      constant := (4044037214459263554782039521592151541514957914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree034.table
  base := (-2654556655466573566552127441150013657969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-20084248032819528329031122483036382486000000000000)
      constant := (173682476628249169589140696008472525282283204316542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17943516384525683757/6250000000000000000)
  centralHi := (287096262152410940113/100000000000000000000)
  directionLo := (145706870723175916143/50000000000000000000)
  directionHi := (291413741446351832287/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree035.table
  base := (-4748018775433226457638419116884732109757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-481942707837125786950139772607814000000000000)
      constant := (4294427294327964505668898440963459877047587987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree035.table
  base := (-474915567112192481812632150233122743037/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-20674264921669886507149428816560234586000000000000)
      constant := (184435386399986015391025456841153756392984928904830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145706870723175916143/50000000000000000000)
  centralHi := (291413741446351832287/100000000000000000000)
  directionLo := (295668181692985904191/100000000000000000000)
  directionHi := (4619815338952904753/1562500000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree036.table
  base := (-1034139274689441275643130269144385295537/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-495696713949090828689415456303214000000000000)
      constant := (4552442880356151759791085888866692865598591868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree036.table
  base := (-129298308067100249813307725310098726093/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (437748558)
      previous := (218874279)
      next := (218874279)
      square := (7069948405873954992904850731238300000000000000)
      linear := (-262521997660743761546515248766470206000000000000)
      constant := (2413774361893443353121279274102996148744677856864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295668181692985904191/100000000000000000000)
  centralHi := (4619815338952904753/1562500000000000000)
  directionLo := (299862266094805356833/100000000000000000000)
  directionHi := (149931133047402678417/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree037.table
  base := (-173705194998786637444866005898970228109/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-509450720061055870428691139998614000000000000)
      constant := (4818076739558233132551904006535474496999832380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree037.table
  base := (-694992632350007058610755665458638985083/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-21854298699370602863386041483607938786000000000000)
      constant := (206923178573443077298510808735865336897809230282985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299862266094805356833/100000000000000000000)
  centralHi := (149931133047402678417/50000000000000000000)
  directionLo := (303998492741966047321/100000000000000000000)
  directionHi := (151999246370983023661/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree038.table
  base := (-690308927010041668688545354759408300077/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-523204726173020912167966823694014000000000000)
      constant := (5091322755538545851467551050796961749377932428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree038.table
  base := (-2761981887135051500226768179729949478539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-22444315588220961041504347817131790886000000000000)
      constant := (218657491109653512515099787904162591565370420064901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303998492741966047321/100000000000000000000)
  centralHi := (151999246370983023661/50000000000000000000)
  directionLo := (61615838402560915843/20000000000000000000)
  directionHi := (19254949500800286201/6250000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree039.table
  base := (-999220025724356736764868351206587972509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-536958732284985953907242507389414000000000000)
      constant := (5372175756107258383828788245705444616399304038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree039.table
  base := (-499771895342975633398631871881841686589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3939737022)
      previous := (1969868511)
      next := (1969868511)
      square := (63629535652865594936143656581144700000000000000)
      linear := (-2559370275230146579958072683406182554000000000000)
      constant := (25635382244396183870342049813267943339220635682156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61615838402560915843/20000000000000000000)
  centralHi := (19254949500800286201/6250000000000000000)
  directionLo := (312106541926211220073/100000000000000000000)
  directionHi := (156053270963105610037/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree040.table
  base := (-37066537438307729222076495313671210023/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-550712738396950995646518191084814000000000000)
      constant := (5660631367515020882955152553155512388251711776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree040.table
  base := (-1186690751357028360970663441533238094553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-23624349365921677397740960484179495086000000000000)
      constant := (243105839232885155306924202676402594297924862618327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312106541926211220073/100000000000000000000)
  centralHi := (156053270963105610037/50000000000000000000)
  directionLo := (158041290866511505003/50000000000000000000)
  directionHi := (316082581733023010007/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree041.table
  base := (-324651773310317870940819165583133753607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-564466744508916037385793874780214000000000000)
      constant := (5956685891193492754218701918989502534007983337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree041.table
  base := (-325138461347599926225484647829887289663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-24214366254772035575859266817703347186000000000000)
      constant := (255819530439392438248573758038757318301403166268817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158041290866511505003/50000000000000000000)
  centralHi := (316082581733023010007/100000000000000000000)
  directionLo := (320009223987197751357/100000000000000000000)
  directionHi := (160004611993598875679/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree042.table
  base := (23427896591495613676305151309953439247/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-578220750620881079125069558475614000000000000)
      constant := (6260336199525551666741411889499370400924285575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree042.table
  base := (585275862049050644307828970220781059631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3939737022)
      previous := (1969868511)
      next := (1969868511)
      square := (63629535652865594936143656581144700000000000000)
      linear := (-2756042571513599305997508127914133254000000000000)
      constant := (29873264492415686565830814292372645977671597953319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320009223987197751357/100000000000000000000)
  centralHi := (160004611993598875679/50000000000000000000)
  directionLo := (161944132649784374627/50000000000000000000)
  directionHi := (64777653059913749851/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree043.table
  base := (772334534031208608968503670967686253983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-591974756732846120864345242171014000000000000)
      constant := (6571579647706542259876192927965194366937011294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree043.table
  base := (308860828061171877516019029816094652771/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-25394400032472751932095879484751051386000000000000)
      constant := (282225276437143981247382579449905052748948928993055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161944132649784374627/50000000000000000000)
  centralHi := (64777653059913749851/20000000000000000000)
  directionLo := (163860697972881190263/50000000000000000000)
  directionHi := (327721395945762380527/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree044.table
  base := (510410474527725141999423682085044221543/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-605728762844811162603620925866414000000000000)
      constant := (6890413999212052595689828582727617170731748435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree044.table
  base := (2551736634575220767944805554042070652841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-25984416921323110110214185818274903486000000000000)
      constant := (295917123111458206658115815541571357887446622751481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163860697972881190263/50000000000000000000)
  centralHi := (327721395945762380527/100000000000000000000)
  directionLo := (331510208474059646941/100000000000000000000)
  directionHi := (165755104237029823471/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree045.table
  base := (901917264531127281982948227577303167193/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-619482768956776204342896609561814000000000000)
      constant := (7216837362771499179706452056039100437203002148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree045.table
  base := (3607396020432070004122556697209413071339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (437748558)
      previous := (218874279)
      next := (218874279)
      square := (7069948405873954992904850731238300000000000000)
      linear := (-328079429755228003559660396935787106000000000000)
      constant := (3826356047477195270983351644930270496871858953579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331510208474059646941/100000000000000000000)
  centralHi := (165755104237029823471/50000000000000000000)
  directionLo := (335256205437557587699/100000000000000000000)
  directionHi := (3352562054375575877/1000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree046.table
  base := (4711368373869034215657054065158623771057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-633236775068741246082172293257214000000000000)
      constant := (7550848139071225200112268438278511839587143713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree046.table
  base := (4711132378352338618598477422196935482079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8593290000000000000000000000000000000000000000
      center := (67027662)
      previous := (33513831)
      next := (33513831)
      square := (1082544084831361728592236123308700000000000000)
      linear := (-51350568429156571770228352524239334000000000000)
      constant := (613002568031294549626940788772233384370879464991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335256205437557587699/100000000000000000000)
  centralHi := (3352562054375575877/1000000000000000000)
  directionLo := (2711686450856914507/800000000000000000)
  directionHi := (10592525198659822293/3125000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree047.table
  base := (73287785509223223984128035674323929991/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-646990781180706287821447976952614000000000000)
      constant := (7892444975685094411442695559891770205861961520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree047.table
  base := (732852369799631613221854483786245825163/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-27754467587874184644569104818846459786000000000000)
      constant := (338947621421538000957659330738549193091342409493464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2711686450856914507/800000000000000000)
  centralHi := (10592525198659822293/3125000000000000000)
  directionLo := (42828169250823632933/12500000000000000000)
  directionHi := (68525070801317812693/20000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree048.table
  base := (7062524658689477786810507815705786541277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-660744787292671329560723660648014000000000000)
      constant := (8241626728962466514202067327729494689416407693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree048.table
  base := (110349196866383658842309514673927065407/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3939737022)
      previous := (1969868511)
      next := (1969868511)
      square := (63629535652865594936143656581144700000000000000)
      linear := (-3149387164080504758076379016930034654000000000000)
      constant := (39326953325640145008758599017664813919353249967552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42828169250823632933/12500000000000000000)
  centralHi := (68525070801317812693/20000000000000000000)
  directionLo := (86562780024823531863/25000000000000000000)
  directionHi := (346251120099294127453/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree049.table
  base := (830978266891391640062029983162188758641/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-674498793404636371299999344343414000000000000)
      constant := (8598392431799526457949268223190162605404223690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree049.table
  base := (8309630701839013170430910390825451951863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-28934501365574901000805717485894163986000000000000)
      constant := (369263192830971014379906964004134158763381171881383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86562780024823531863/25000000000000000000)
  centralHi := (346251120099294127453/100000000000000000000)
  directionLo := (87459827610984895743/25000000000000000000)
  directionHi := (349839310443939582973/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree050.table
  base := (600294986557841796705119792563726741559/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-688252799516601413039275028038814000000000000)
      constant := (8962741266385747398202678703414637232019190896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree050.table
  base := (9604588667846123847054455651121113888519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-29524518254425259178924023819418016086000000000000)
      constant := (384909425301988393848411694047938638802978079044279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87459827610984895743/25000000000000000000)
  centralHi := (349839310443939582973/100000000000000000000)
  directionLo := (176695534814668183411/50000000000000000000)
  directionHi := (353391069629336366823/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree051.table
  base := (2189454164043374196494894756017646148139/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-702006805628566454778550711734214000000000000)
      constant := (9334672541157473772837898503853270039928033255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree051.table
  base := (10947157737748847233780973659662823195209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3939737022)
      previous := (1969868511)
      next := (1969868511)
      square := (63629535652865594936143656581144700000000000000)
      linear := (-3346059460363957484115814461437985354000000000000)
      constant := (44542360878334777759915484829614305479374426029841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176695534814668183411/50000000000000000000)
  centralHi := (353391069629336366823/100000000000000000000)
  directionLo := (356907485289453958161/100000000000000000000)
  directionHi := (178453742644726979081/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree052.table
  base := (12337380651257712492817149140362571268371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-715760811740531496517826395429614000000000000)
      constant := (9714185671309171455657570484030434518586147939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree052.table
  base := (12337283160311047392926161627855785933387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-30704552032125975535160636486465720286000000000000)
      constant := (417178635750951908696476180031694711562615952663867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356907485289453958161/100000000000000000000)
  centralHi := (178453742644726979081/50000000000000000000)
  directionLo := (180194795996941267681/50000000000000000000)
  directionHi := (360389591993882535363/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree053.table
  base := (13775002664070098857081724339472451607613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-729514817852496538257102079125014000000000000)
      constant := (10101280162313148964746884474703205239105166317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree053.table
  base := (344372966150216724109302629100415572083/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-31294568920976333713278942819989572386000000000000)
      constant := (433801567797279929843756671864858646546095560416120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180194795996941267681/50000000000000000000)
  centralHi := (360389591993882535363/100000000000000000000)
  directionLo := (363838374803143122377/100000000000000000000)
  directionHi := (181919187401571561189/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree054.table
  base := (15260097440605873410004503217607917729379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-743268823964461579996377762820414000000000000)
      constant := (10495955595983333406044057923312158399190981811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree054.table
  base := (15260025059303736253234772254770184298711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (437748558)
      previous := (218874279)
      next := (218874279)
      square := (7069948405873954992904850731238300000000000000)
      linear := (-393636861849712245572805545105104006000000000000)
      constant := (5564815138932925037564999725715741966284038224471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363838374803143122377/100000000000000000000)
  centralHi := (181919187401571561189/50000000000000000000)
  directionLo := (73450954504694568033/20000000000000000000)
  directionHi := (183627386261736420083/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree055.table
  base := (3358526329581471892275655767141428149401/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-757022830076426621735653446515814000000000000)
      constant := (10898211618690376787542682571440787056184976045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree055.table
  base := (1679256931302160118077498822081645421791/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-32474602698677050069515555487037276586000000000000)
      constant := (468023996078878259322466878836148310124123240284310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73450954504694568033/20000000000000000000)
  centralHi := (183627386261736420083/50000000000000000000)
  directionLo := (370639680691562099081/100000000000000000000)
  directionHi := (185319840345781049541/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree056.table
  base := (18372577098748047912193231584026691901557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-770776836188391663474929130211214000000000000)
      constant := (11308047931395993074211363242849323174383618213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree056.table
  base := (18372523433597331895781429818914253699459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-33064619587527408247633861820561128686000000000000)
      constant := (485623464556849762221117269748185234809452971192819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370639680691562099081/100000000000000000000)
  centralHi := (185319840345781049541/50000000000000000000)
  directionLo := (186996977158066942889/50000000000000000000)
  directionHi := (373993954316133885779/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree057.table
  base := (3999981991456394330029302802696915212793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-784530842300356705214204813906614000000000000)
      constant := (11725464281225692400955679028950455867462604685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree057.table
  base := (4999965942696055007970446632684351726937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3939737022)
      previous := (1969868511)
      next := (1969868511)
      square := (63629535652865594936143656581144700000000000000)
      linear := (-3739404052930862936194685350453886754000000000000)
      constant := (55949824548492563017319305635649759714599145310852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186996977158066942889/50000000000000000000)
  centralHi := (373993954316133885779/100000000000000000000)
  directionLo := (377318410400147012567/100000000000000000000)
  directionHi := (47164801300018376571/12500000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree058.table
  base := (10837305033658429748544229206616533060273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-798284848412321746953480497602014000000000000)
      constant := (12150460454342430962846640104999801598472872514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree058.table
  base := (10837285164749232082619935092587780015563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-34244653365228124603870474487608832886000000000000)
      constant := (521798856128162184458045889777088202786947373986166) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377318410400147012567/100000000000000000000)
  centralHi := (47164801300018376571/12500000000000000000)
  directionLo := (380613830264704252169/100000000000000000000)
  directionHi := (38061383026470425217/10000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree059.table
  base := (23396660384281705030147676398742655282297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-812038854524286788692756181297414000000000000)
      constant := (12583036269920354952744003911625886829889888873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree059.table
  base := (11698313102462226941592695624559222387537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-34834670254078482781988780821132684986000000000000)
      constant := (540374762447360816770749936430015528705933250068034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380613830264704252169/100000000000000000000)
  centralHi := (38061383026470425217/10000000000000000000)
  directionLo := (383880961693393213561/100000000000000000000)
  directionHi := (191940480846696606781/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree060.table
  base := (12583023247440748966008602951123065710901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-825792860636251830432031864992814000000000000)
      constant := (13023191575048817606191460888251769208253897418) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree060.table
  base := (12583008552461103840966606721172572972141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3939737022)
      previous := (1969868511)
      next := (1969868511)
      square := (63629535652865594936143656581144700000000000000)
      linear := (-3936076349214315662234120794961837454000000000000)
      constant := (62141792599670658291594275872055000329470268520618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383880961693393213561/100000000000000000000)
  centralHi := (191940480846696606781/50000000000000000000)
  directionLo := (12097516278554146889/3125000000000000000)
  directionHi := (387120520913732700449/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree061.table
  base := (26982756210902893400263305201495578251553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-839546866748216872171307548688214000000000000)
      constant := (13470926240423063548179991468946120589670725777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree061.table
  base := (5396546189248963704120582336576946245297/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-36014704031779199138225393488180389186000000000000)
      constant := (578502963484324217368539712320541440938865664010885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12097516278554146889/3125000000000000000)
  centralHi := (387120520913732700449/100000000000000000000)
  directionLo := (390333194430598083097/100000000000000000000)
  directionHi := (195166597215299041549/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree062.table
  base := (3605847403215521544832387448222387081823/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-853300872860181913910583232383614000000000000)
      constant := (13926240156700142961029904739902998436408481656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree062.table
  base := (5769351502631781357198698351813803445933/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-36604720920629557316343699821704241286000000000000)
      constant := (598055248065306117786788086751202898801176970441265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390333194430598083097/100000000000000000000)
  centralHi := (195166597215299041549/50000000000000000000)
  directionLo := (78703928144984076311/20000000000000000000)
  directionHi := (98379910181230095389/25000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree063.table
  base := (30758106823849856096403540276955287012581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-867054878972146955649858916079014000000000000)
      constant := (14389133231417364311098312374635100639916471829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree063.table
  base := (30758088168823977339129993684547664210387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (437748558)
      previous := (218874279)
      next := (218874279)
      square := (7069948405873954992904850731238300000000000000)
      linear := (-459194293944196487585950693274420906000000000000)
      constant := (7628802261898804139331881151322357381722629716307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78703928144984076311/20000000000000000000)
  centralHi := (98379910181230095389/25000000000000000000)
  directionLo := (6198132684836956281/1562500000000000000)
  directionHi := (79336098365913040397/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree064.table
  base := (32716731635284577844580895276335132722661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-880808885084111997389134599774414000000000000)
      constant := (14859605386386446752333787372368335423054710549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree064.table
  base := (32716715611277027240735535279361658775801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-37784754698330273672580312488751945486000000000000)
      constant := (638136165610452118794188269842136750812425507392841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6198132684836956281/1562500000000000000)
  centralHi := (79336098365913040397/20000000000000000000)
  directionLo := (399816354793073809111/100000000000000000000)
  directionHi := (49977044349134226139/12500000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree065.table
  base := (8680661856956097067788889996153125923963/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-894562891196077039128410283469814000000000000)
      constant := (15337656555489938586272764003908664051709293868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree065.table
  base := (34722633667128859021443841215704500283749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-38374771587180631850698618822275797586000000000000)
      constant := (658664792448922686871136811992372100945372550798709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399816354793073809111/100000000000000000000)
  centralHi := (49977044349134226139/12500000000000000000)
  directionLo := (402927813040867660997/100000000000000000000)
  directionHi := (201463906520433830499/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree066.table
  base := (18387924465706094698764691521226576547099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-908316897308042080867685967165214000000000000)
      constant := (15823286682817804060460294481484909501176346582) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree066.table
  base := (18387918558571959561928531078296421527013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3939737022)
      previous := (1969868511)
      next := (1969868511)
      square := (63629535652865594936143656581144700000000000000)
      linear := (-4329420941781221114312991683977738854000000000000)
      constant := (75502095706292047934908955834850289034002330491674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402927813040867660997/100000000000000000000)
  centralHi := (201463906520433830499/50000000000000000000)
  directionLo := (203007713821280528221/50000000000000000000)
  directionHi := (406015427642561056443/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree067.table
  base := (38876331689607562775041115280960486194441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-922070903420007122606961650860614000000000000)
      constant := (16316495721091666775574531612664247798036824569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree067.table
  base := (38876321548776199026926641681605852729321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-39554805364881348206935231489323501786000000000000)
      constant := (700698370327691944225392434022610433670798348687161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203007713821280528221/50000000000000000000)
  centralHi := (406015427642561056443/100000000000000000000)
  directionLo := (204539869246589100109/50000000000000000000)
  directionHi := (409079738493178200219/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree068.table
  base := (41024091933985345500068776282687381252213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-935824909531972164346237334556014000000000000)
      constant := (16817283630332304178370949807197982427704727717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree068.table
  base := (16409633292598101165710852752218280431/4000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-40144822253731706385053537822847353886000000000000)
      constant := (722203317666269889641586995059594953974689081677500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204539869246589100109/50000000000000000000)
  centralHi := (409079738493178200219/100000000000000000000)
  directionLo := (412121265415317280729/100000000000000000000)
  directionHi := (41212126541531728073/10000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree069.table
  base := (540239080974043046832334958965042763063/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-949578915643937206085513018251414000000000000)
      constant := (17325650376732842475449243800059577093866829360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree069.table
  base := (8643823802276042692663760617527455891067/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (7447518)
      previous := (3723759)
      next := (3723759)
      square := (120282676092373525399137347034300000000000000)
      linear := (-8555941848893523327698349959330226000000000000)
      constant := (156276769993412522764160737899246139079674841135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (412121265415317280729/100000000000000000000)
  centralHi := (41212126541531728073/10000000000000000000)
  directionLo := (415140509188633289509/100000000000000000000)
  directionHi := (41514050918863328951/10000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree070.table
  base := (45461432626786766043211172391510550479333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-963332921755902247824788701946814000000000000)
      constant := (17841595931705897981389500690765515430035243797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree070.table
  base := (22730713111002007299559965303481056438753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-41324856031432422741290150489895058086000000000000)
      constant := (766189521932675480785956721115663363737867692987746) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415140509188633289509/100000000000000000000)
  centralHi := (41514050918863328951/10000000000000000000)
  directionLo := (418137952512413120659/100000000000000000000)
  directionHi := (20906897625620656033/5000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree071.table
  base := (5968876012747025605184343939803600800269/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-977086927867867289564064385642214000000000000)
      constant := (18365120271077812764210032466005605207120430568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree071.table
  base := (11937750652272558543084721422180552661921/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-41914872920282780919408456823418910186000000000000)
      constant := (788670776623624929570857566563418742370888067695044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418137952512413120659/100000000000000000000)
  centralHi := (20906897625620656033/5000000000000000000)
  directionLo := (421114060906482175431/100000000000000000000)
  directionHi := (52639257613310271929/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree072.table
  base := (12521962744175578866815025811093878092169/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-990840933979832331303340069337614000000000000)
      constant := (18896223374407277605363127301854187810719283684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree072.table
  base := (10017569253362810259552729783575232879101/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (437748558)
      previous := (218874279)
      next := (218874279)
      square := (7069948405873954992904850731238300000000000000)
      linear := (-524751726038680729599095841443737806000000000000)
      constant := (10018240310433653245604321572124661844650041736305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (421114060906482175431/100000000000000000000)
  centralHi := (52639257613310271929/12500000000000000000)
  directionLo := (212034641777601820093/50000000000000000000)
  directionHi := (424069283555203640187/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree073.table
  base := (13117989905418436704311454910354291407073/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1004594940091797373042615753033014000000000000)
      constant := (19434905224409140560993648381603816710150549828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree073.table
  base := (52471955583947764133431228881014208182283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-43094906697983497275645069490466614386000000000000)
      constant := (834609586764738419853069641479552438476125653028603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212034641777601820093/50000000000000000000)
  centralHi := (424069283555203640187/100000000000000000000)
  directionLo := (427004054098903184897/100000000000000000000)
  directionHi := (213502027049451592449/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree074.table
  base := (13725833164792469744016490991472555204813/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1018348946203762414781891436728414000000000000)
      constant := (19981165806467163574419478482340965352671444468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree074.table
  base := (54903329198329427097633512020076903980669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-43684923586833855453763375823990466486000000000000)
      constant := (858067140863244006567315797323960124033205480572429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427004054098903184897/100000000000000000000)
  centralHi := (213502027049451592449/50000000000000000000)
  directionLo := (8598375827533345663/2000000000000000000)
  directionHi := (429918791376667283151/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree075.table
  base := (57381968924203392804538061609784175748711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1032102952315727456521167120423814000000000000)
      constant := (20535005108221996176893030730949250320518074999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree075.table
  base := (14345491489592074662079657717082443160269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3939737022)
      previous := (1969868511)
      next := (1969868511)
      square := (63629535652865594936143656581144700000000000000)
      linear := (-4919437830631579292431298017501590954000000000000)
      constant := (97983347435238527619730495942092067416396023527124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8598375827533345663/2000000000000000000)
  centralHi := (429918791376667283151/100000000000000000000)
  directionLo := (86562780024823531863/20000000000000000000)
  directionHi := (108203475031029414829/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree076.table
  base := (59907867431678293574242039771240249488349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1045856958427692498260442804119214000000000000)
      constant := (21096423119222754960340496575073751806821894541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree076.table
  base := (11981572978099916860715252824985928843881/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-44864957364534571809999988491038170686000000000000)
      constant := (905958544483878653868129862777290920875593634920605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86562780024823531863/20000000000000000000)
  centralHi := (108203475031029414829/25000000000000000000)
  directionLo := (435689771629453134761/100000000000000000000)
  directionHi := (217844885814726567381/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree077.table
  base := (15620256837154466296305162078885824510049/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1059610964539657539999718487814614000000000000)
      constant := (21665419830632389943657429548035276848908439364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree077.table
  base := (62481025171669030512567565107752489224349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-45454974253384929988118294824562022786000000000000)
      constant := (930392393189291570843349522515961000503902748363309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435689771629453134761/100000000000000000000)
  centralHi := (217844885814726567381/50000000000000000000)
  directionLo := (87709356870153906051/20000000000000000000)
  directionHi := (27409174021923095641/6250000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree078.table
  base := (65101447970679904545660860663405979958653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1073364970651622581738994171510014000000000000)
      constant := (22241995234978534694242785250854166041381349677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree078.table
  base := (65101446106070021326090388738178063878011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3939737022)
      previous := (1969868511)
      next := (1969868511)
      square := (63629535652865594936143656581144700000000000000)
      linear := (-5116110126915032018470733462009541654000000000000)
      constant := (106127963635231357829321570184109590432365138825939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87709356870153906051/20000000000000000000)
  centralHi := (27409174021923095641/6250000000000000000)
  directionLo := (88277060899482983239/20000000000000000000)
  directionHi := (110346326124353729049/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree079.table
  base := (33884564351148701742753130315267877927113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1087118976763587623478269855205414000000000000)
      constant := (22826149325942818822420435164231259833857483634) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree079.table
  base := (33884563552737982906435497316460161739621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-46635008031085646344354907491609726986000000000000)
      constant := (980236382799851593773980388746007418692544487218922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88277060899482983239/20000000000000000000)
  centralHi := (110346326124353729049/25000000000000000000)
  directionLo := (111051421644477106377/25000000000000000000)
  directionHi := (444205686577908425509/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree080.table
  base := (70484069039885012773955567487121645700247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1100872982875552665217545538900814000000000000)
      constant := (23417882098182705358200808500903993539233920423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree080.table
  base := (70484067672612333687490110402697598141237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-47225024919936004522473213825133579086000000000000)
      constant := (1005646523211546128035555232141752539041635745435717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111051421644477106377/25000000000000000000)
  centralHi := (444205686577908425509/100000000000000000000)
  directionLo := (223504136958371725133/50000000000000000000)
  directionHi := (447008273916743450267/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree081.table
  base := (73246268557638018494043011580419119058459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1114626988987517706956821222596214000000000000)
      constant := (24017193547180832091638815410626400434091191531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree081.table
  base := (73246267387098569019253592870753535850619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (437748558)
      previous := (218874279)
      next := (218874279)
      square := (7069948405873954992904850731238300000000000000)
      linear := (-590309158133164971612240989613054706000000000000)
      constant := (12733112268655149518460015698885876770512945777659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223504136958371725133/50000000000000000000)
  centralHi := (447008273916743450267/100000000000000000000)
  directionLo := (1799173596568832141/400000000000000000)
  directionHi := (449793399142208035251/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree082.table
  base := (76055726895523619834994736634006246001691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1128380995099482748696096906291614000000000000)
      constant := (24624083669117611038932956052161920263831939819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree082.table
  base := (19013931473390678273353693974799522344149/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-48405058697636720878709826492181283286000000000000)
      constant := (1057443094286867766230505086619111798028381557100436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1799173596568832141/400000000000000000)
  centralHi := (449793399142208035251/100000000000000000000)
  directionLo := (226280692323592315693/50000000000000000000)
  directionHi := (452561384647184631387/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree083.table
  base := (78912443749126078100523915797381922930667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1142135001211447790435372589987014000000000000)
      constant := (25238552460763495628254323479453586820371446203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree083.table
  base := (78912442891592948498766977208010831881771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-48995075586487079056828132825705135386000000000000)
      constant := (1083829524652385375406528773646082818677418977187611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226280692323592315693/50000000000000000000)
  centralHi := (452561384647184631387/100000000000000000000)
  directionLo := (56914067878092035627/12500000000000000000)
  directionHi := (455312543024736285017/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree084.table
  base := (4090820943052977519405599918218040112947/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1155889007323412832174648273682414000000000000)
      constant := (25860599919387879452250098388059479751165094460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree084.table
  base := (81816418127242171348244531049003962097/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3939737022)
      previous := (1969868511)
      next := (1969868511)
      square := (63629535652865594936143656581144700000000000000)
      linear := (-5509454719481937470549604351025443054000000000000)
      constant := (123393487193575487098999925295204092560336354553000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56914067878092035627/12500000000000000000)
  centralHi := (455312543024736285017/100000000000000000000)
  directionLo := (91609435496029045219/20000000000000000000)
  directionHi := (28627948592509076631/6250000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree085.table
  base := (10595956501713325025602160971507950915447/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1169643013435377873913923957377814000000000000)
      constant := (26490226042682059127166662319144012810095817784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree085.table
  base := (84767651385845573245451841821520647783729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-50175109364187795413064745492752839586000000000000)
      constant := (1137578674458666380957784112573029835415113006597889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91609435496029045219/20000000000000000000)
  centralHi := (28627948592509076631/6250000000000000000)
  directionLo := (460765582220941269429/100000000000000000000)
  directionHi := (46076558222094126943/10000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree086.table
  base := (87766143023077736215707859050513056828181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1183397019547342915653199641073214000000000000)
      constant := (27127430828694090139431722480700697019890172229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree086.table
  base := (87766142485948308663668291976915133766077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-50765126253038153591183051826276691686000000000000)
      constant := (1164941393719359708213470169870765375682572597454157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460765582220941269429/100000000000000000000)
  centralHi := (46076558222094126943/10000000000000000000)
  directionLo := (463468042826340205183/100000000000000000000)
  directionHi := (3620844084580782853/781250000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree087.table
  base := (45405945866809461076736802493644917277249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1197151025659307957392475324768614000000000000)
      constant := (27772214275773699718285385945312975854788669282) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree087.table
  base := (45405945637085842361916978916175291746353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3939737022)
      previous := (1969868511)
      next := (1969868511)
      square := (63629535652865594936143656581144700000000000000)
      linear := (-5706127015765390196589039795533393754000000000000)
      constant := (132514393606059522918567070677913799945045075578994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463468042826340205183/100000000000000000000)
  centralHi := (3620844084580782853/781250000000000000)
  directionLo := (116538709149351328261/25000000000000000000)
  directionHi := (93230967319481062609/20000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree088.table
  base := (18780979602764143183347496918288264504881/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1210905031771272999131751008464014000000000000)
      constant := (28424576382525704192474143685107832990661412645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree088.table
  base := (23476224405218206228103954347180857146933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-51945160030738869947419664493324395886000000000000)
      constant := (1220643120605260662783422165404089909290214723317012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116538709149351328261/25000000000000000000)
  centralHi := (93230967319481062609/20000000000000000000)
  directionLo := (46882623288914729531/10000000000000000000)
  directionHi := (468826232889147295311/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree089.table
  base := (97045161752505286885083306745334888356841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1224659037883238040871026692159414000000000000)
      constant := (29084517147770617956946000328518303830577726169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree089.table
  base := (97045161416475175114831827045796604289033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-52535176919589228125537970826848247986000000000000)
      constant := (1248982128121722715417609760791484951342390842155353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46882623288914729531/10000000000000000000)
  centralHi := (468826232889147295311/100000000000000000000)
  directionLo := (235741246712844200559/50000000000000000000)
  directionHi := (471482493425688401119/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree090.table
  base := (50116341427843332050592912020237492892437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1238413043995203082610302375854814000000000000)
      constant := (29752036570511343845814692325787659124191728266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree090.table
  base := (25058170642091543184925368035703297204241/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (437748558)
      previous := (218874279)
      next := (218874279)
      square := (7069948405873954992904850731238300000000000000)
      linear := (-655866590227649213625386137782371606000000000000)
      constant := (15773414382244710846999365984688247398564201499204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235741246712844200559/50000000000000000000)
  centralHi := (471482493425688401119/100000000000000000000)
  directionLo := (474123872599534515009/100000000000000000000)
  directionHi := (47412387259953451501/10000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree091.table
  base := (103467461243915722560293941456786345120669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1252167050107168124349578059550214000000000000)
      constant := (30427134649905006091904815309847920335385177421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree091.table
  base := (51733730499137211543444285739109867968133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-53715210697289944481774583493895952186000000000000)
      constant := (1306636431089976247182550228671787570493596652996906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474123872599534515009/100000000000000000000)
  centralHi := (47412387259953451501/10000000000000000000)
  directionLo := (119187654438980949809/25000000000000000000)
  directionHi := (476750617755923799237/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree092.table
  base := (53374748425017537823092654927436469588919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1265921056219133166088853743245614000000000000)
      constant := (31109811385239131980604866378679235011737683342) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree092.table
  base := (53374748320026137067884085386838925076119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8593290000000000000000000000000000000000000000
      center := (67027662)
      previous := (33513831)
      next := (33513831)
      square := (1082544084831361728592236123308700000000000000)
      linear := (-102656384850926848128341946743704734000000000000)
      constant := (2525428594472810941471767457167035841293472528302) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119187654438980949809/25000000000000000000)
  centralHi := (476750617755923799237/100000000000000000000)
  directionLo := (479362969463151475749/100000000000000000000)
  directionHi := (1917451877852605903/400000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree093.table
  base := (110078789617280593726689454568639209435309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1279675062331098207828129426941014000000000000)
      constant := (31800066775911510860647148966548995372899193181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree093.table
  base := (110078789437801134309354350060742208344837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3939737022)
      previous := (1969868511)
      next := (1969868511)
      square := (63629535652865594936143656581144700000000000000)
      linear := (-6099471608332295648667910684549295154000000000000)
      constant := (151732494566092570847902946020354752446540918864813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479362969463151475749/100000000000000000000)
  centralHi := (1917451877852605903/400000000000000000)
  directionLo := (240980580884853470553/50000000000000000000)
  directionHi := (481961161769706941107/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree094.table
  base := (56727669748838018805021411537135288063193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1293429068443063249567405110636414000000000000)
      constant := (32497900821413162810446243544732052542124829074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree094.table
  base := (56727669672143280534385765308432405910633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-55485261363841019016129502494467508486000000000000)
      constant := (1395558604924652624962087917649791796807227489281906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240980580884853470553/50000000000000000000)
  centralHi := (481961161769706941107/100000000000000000000)
  directionLo := (242272711224500557043/50000000000000000000)
  directionHi := (484545422449001114087/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree095.table
  base := (58439573225337778125723250526541241140803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1307183074555028291306680794331814000000000000)
      constant := (33203313521313936896267878431221482054525558054) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree095.table
  base := (116879146319598334969613520329028785848971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-56075278252691377194247808827991360586000000000000)
      constant := (1425850187947432861288994809178809381775334701842811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242272711224500557043/50000000000000000000)
  centralHi := (484545422449001114087/100000000000000000000)
  directionLo := (121778993308102065419/25000000000000000000)
  directionHi := (487115973232408261677/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree096.table
  base := (60175105221007891788625036809998288814071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1320937080666993333045956478027214000000000000)
      constant := (33916304875250333067436696374501487692056958478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree096.table
  base := (12035021033001765534834546700390121700919/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (3939737022)
      previous := (1969868511)
      next := (1969868511)
      square := (63629535652865594936143656581144700000000000000)
      linear := (-6296143904615748374707346129057245854000000000000)
      constant := (161829688905316198247749263420112260505563614836310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121778993308102065419/25000000000000000000)
  centralHi := (487115973232408261677/100000000000000000000)
  directionLo := (489673030031297120221/100000000000000000000)
  directionHi := (244836515015648560111/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree097.table
  base := (61934265721372588208240103381163541217889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1334691086778958374785232161722614000000000000)
      constant := (34636874882915204402451841274031486017561168802) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree097.table
  base := (7741783209191215352556447746714951072559/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-57255312030392093550484421495039064786000000000000)
      constant := (1487409641512942504086570335929750724370115631838704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell099.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489673030031297120221/100000000000000000000)
  centralHi := (244836515015648560111/50000000000000000000)
  directionLo := (492216803148680551689/100000000000000000000)
  directionHi := (49221680314868055169/10000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree098.table
  base := (63717054714201615380966681757763632347719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (13364741788041502822126371892700000000000000)
      linear := (-1348445092890923416524507845418014000000000000)
      constant := (35365023544049049414300890806154600751153901742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree098.table
  base := (127434109346662703785365131698582129548989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (35457633198)
      previous := (17728816599)
      next := (17728816599)
      square := (572665820875790354425292909230302300000000000000)
      linear := (-57845328919242451728602727828562916886000000000000)
      constant := (1518677512031785249250656044345443604680894476073549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell099.Kernel098
