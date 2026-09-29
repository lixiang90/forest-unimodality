import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell065.Parameters
import ForestUnimodality.BinomialMassData.Q203_404.Batch000_049
import ForestUnimodality.BinomialMassData.Q203_404.Batch050_099
import ForestUnimodality.BinomialMassData.Q203_404.Batch100_149
import ForestUnimodality.BinomialMassData.Q407_808.Batch000_049
import ForestUnimodality.BinomialMassData.Q407_808.Batch050_099
import ForestUnimodality.BinomialMassData.Q407_808.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree000.table
  base := (6292493585042458996813508047/100000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (126)
      previous := (63)
      next := (63)
      square := (757634017127069431252195390000000000000)
      linear := (-6892521862655144127343676000000000000)
      constant := (629249358504245899681350804700000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree000.table
  base := (6292493585042458996813508047/100000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (126)
      previous := (63)
      next := (63)
      square := (757634017127069431252195390000000000000)
      linear := (-6892521862655144127343676000000000000)
      constant := (629249358504245899681350804700000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree001.table
  base := (355410051097125286763536607893287595119351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-7837195742099097399724913879461000000000000)
      constant := (3627524594348949392641877151455840632812499551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree001.table
  base := (11085551903416083403469917629671116060351/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-7856326001031555902864031813058500000000000)
      constant := (3620675253380805613253595849283688726562497632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24999310719838117927/50000000000000000000)
  directionHi := (9999724287935247171/20000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree002.table
  base := (104869797702153313413781380156068346546907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-15604080868677249674206794920046000000000000)
      constant := (2147429606460154260526107111595247906249996614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree002.table
  base := (104513429420122793789453343702855058633957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-15642341386542166680485030787241000000000000)
      constant := (2140197652084839900408431229482863781249990714) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24999310719838117927/50000000000000000000)
  centralHi := (9999724287935247171/20000000000000000000)
  directionLo := (70708728539948335741/100000000000000000000)
  directionHi := (35354364269974167871/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree003.table
  base := (13072789445510054081993794287337244812533/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-23370965995255401948688675960631000000000000)
      constant := (1351223243237424670577484493195455218326491330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree003.table
  base := (32537806187585332886614181239360953755821/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-23428356772052777458106029761423500000000000)
      constant := (1345427515510055880577106292277868075802520084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70708728539948335741/100000000000000000000)
  centralHi := (35354364269974167871/50000000000000000000)
  directionLo := (3464006105676872263/4000000000000000000)
  directionHi := (5412509540120112911/6250000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree004.table
  base := (86608873524654278496589008996334634737903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-31137851121833554223170557001216000000000000)
      constant := (914859776412537717556219127987147608961348503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree004.table
  base := (8618318502528567284528312742818237697989/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-31214372157563388235727028735606000000000000)
      constant := (910671665216813712253928269679081927571857890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3464006105676872263/4000000000000000000)
  centralHi := (5412509540120112911/6250000000000000000)
  directionLo := (99997242879352471709/100000000000000000000)
  directionHi := (9999724287935247171/10000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree005.table
  base := (6094842719210684384054440864751206949927/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-38904736248411706497652438041801000000000000)
      constant := (670694896587290381093184234078477495962053270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree005.table
  base := (60642793932723180759325557695486178886707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-39000387543073999013348027709788500000000000)
      constant := (667818174789355646704365662700498729573298107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99997242879352471709/100000000000000000000)
  centralHi := (9999724287935247171/10000000000000000000)
  directionLo := (111800316320394464073/100000000000000000000)
  directionHi := (55900158160197232037/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree006.table
  base := (11034576607803993010188206172488392251/2441406250000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-46671621374989858772134319082386000000000000)
      constant := (531520972178701336989750594907299049987639296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree006.table
  base := (44976542972811827859299327731878736081119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-46786402928584609790969026683971000000000000)
      constant := (529612704020793162122285368773830861763494919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111800316320394464073/100000000000000000000)
  centralHi := (55900158160197232037/50000000000000000000)
  directionLo := (122471110369786036779/100000000000000000000)
  directionHi := (6123555518489301839/5000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree007.table
  base := (17448260613423052977702244697134055126889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-54438506501568011046616200122971000000000000)
      constant := (451842072841224709425600961210414867698789378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree007.table
  base := (17365901474071380731410838826948428804081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-54572418314095220568590025658153500000000000)
      constant := (450633982468358552294700854327870313210860562) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122471110369786036779/100000000000000000000)
  centralHi := (6123555518489301839/5000000000000000000)
  directionLo := (132283918225445548911/100000000000000000000)
  directionHi := (8267744889090346807/6250000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree008.table
  base := (13848174495975168519685220938180135077423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-62205391628146163321098081163556000000000000)
      constant := (407698451665543041748590611664847115849584046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree008.table
  base := (27568480167330540389939658604667593433481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-62358433699605831346211024632336000000000000)
      constant := (407010714386228931744912088073656120614939681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132283918225445548911/100000000000000000000)
  centralHi := (8267744889090346807/6250000000000000000)
  directionLo := (70708728539948335741/50000000000000000000)
  directionHi := (141417457079896671483/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree009.table
  base := (11171845817812395965595256910982838539061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-69972276754724315595579962204141000000000000)
      constant := (386303997292629902659559099744891746873922522) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree009.table
  base := (5560022443592629686327915004676745366527/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-70144449085116442123832023606518500000000000)
      constant := (386027507758300907694539300632686386685767708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70708728539948335741/50000000000000000000)
  centralHi := (141417457079896671483/100000000000000000000)
  directionLo := (37498966079757176891/25000000000000000000)
  directionHi := (29999172863805741513/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree010.table
  base := (4539067643626508598484161301340725311167/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-77739161881302467870061843244726000000000000)
      constant := (380698785893594879105603285128164455596858268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree010.table
  base := (903457665056622721260990045617548656821/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-77930464470627052901453022580701000000000000)
      constant := (380773404731177880443556388090604151964620420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37498966079757176891/25000000000000000000)
  centralHi := (29999172863805741513/20000000000000000000)
  directionLo := (31621904723580786551/20000000000000000000)
  directionHi := (39527380904475983189/25000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree011.table
  base := (14751764639166175329778681096500354537147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-85506047007880620144543724285311000000000000)
      constant := (386982759219104074399757757373208991633436547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree011.table
  base := (14676426024009905693010331778105992374027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-85716479856137663679074021554883500000000000)
      constant := (387379729879350537836358451721467446957449427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31621904723580786551/20000000000000000000)
  centralHi := (39527380904475983189/25000000000000000000)
  directionLo := (6633066694017007837/4000000000000000000)
  directionHi := (82913333675212597963/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree012.table
  base := (2976792933560674421074286532848762870487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-93272932134458772419025605325896000000000000)
      constant := (402881072894364452069889448292034920167351548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree012.table
  base := (5920390627066769666317722215677437244191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-93502495241648274456695020529066000000000000)
      constant := (403590769849662811736041800233996574655984782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6633066694017007837/4000000000000000000)
  centralHi := (82913333675212597963/50000000000000000000)
  directionLo := (173200305283843613151/100000000000000000000)
  directionHi := (5412509540120112911/3125000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree013.table
  base := (9485582306216913154227828513986895680173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-101039817261036924693507486366481000000000000)
      constant := (426997112563931872734400133353033197833444773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree013.table
  base := (9426411596420878362483860512044050010599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-101288510627158885234316019503248500000000000)
      constant := (428021153404878354453189783077285072908120399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173200305283843613151/100000000000000000000)
  centralHi := (5412509540120112911/3125000000000000000)
  directionLo := (22534074162908226599/12500000000000000000)
  directionHi := (180272593303265812793/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree014.table
  base := (3698907415824053101539054267856999365389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-108806702387615076967989367407066000000000000)
      constant := (458421137507187597205528598909164001052666378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree014.table
  base := (7344764884300157424659899886231006341951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-109074526012669496011937018477431000000000000)
      constant := (459767559893798587571908567204985370694242151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22534074162908226599/12500000000000000000)
  centralHi := (180272593303265812793/100000000000000000000)
  directionLo := (187077711238278543689/100000000000000000000)
  directionHi := (18707771123827854369/10000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree015.table
  base := (1395530085618800941186175043189849485277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-116573587514193229242471248447651000000000000)
      constant := (496523246500940619135955224231470493397242708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree015.table
  base := (5534443488709617591485658129894308870613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-116860541398180106789558017451613500000000000)
      constant := (498203672102364508270955849587654813539123213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187077711238278543689/100000000000000000000)
  centralHi := (18707771123827854369/10000000000000000000)
  directionLo := (9682191408459758171/5000000000000000000)
  directionHi := (193643828169195163421/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree016.table
  base := (499160533228363154741959076712238711189/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-124340472640771381516953129488236000000000000)
      constant := (540842205687330801091901023112604376742711912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree016.table
  base := (3950426138507938916341884325064790706493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-124646556783690717567179016425796000000000000)
      constant := (542870228043663511774868651611089929996935093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9682191408459758171/5000000000000000000)
  centralHi := (193643828169195163421/100000000000000000000)
  directionLo := (199994485758704943419/100000000000000000000)
  directionHi := (9999724287935247171/5000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree017.table
  base := (519328342371011485141593372004278395161/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-132107357767349533791435010528821000000000000)
      constant := (591024398525017132311349850708784094545186805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree017.table
  base := (2558154364212835218174068954899140061341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-132432572169201328344800015399978500000000000)
      constant := (593414696770506796750709921693972096515739541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199994485758704943419/100000000000000000000)
  centralHi := (9999724287935247171/5000000000000000000)
  directionLo := (206149597331056862241/100000000000000000000)
  directionHi := (103074798665528431121/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree018.table
  base := (272936649703136310705778281621312808079/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-139874242893927686065916891569406000000000000)
      constant := (646789201297718985315293720991548559776069395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree018.table
  base := (1330179137991836655483508314815929593613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-140218587554711939122421014374161000000000000)
      constant := (649557070749975338345351383345866172784446213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206149597331056862241/100000000000000000000)
  centralHi := (103074798665528431121/50000000000000000000)
  directionLo := (212126185619845007223/100000000000000000000)
  directionHi := (26515773202480625903/12500000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree019.table
  base := (275044151081779977113732280412027389499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-147641128020505838340398772609991000000000000)
      constant := (707908471448496257134384266675997966400279299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree019.table
  base := (244172867739103072380204140745164833627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-148004602940222549900042013348343500000000000)
      constant := (711069586214997461128559164274994145217829027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212126185619845007223/100000000000000000000)
  centralHi := (26515773202480625903/12500000000000000000)
  directionLo := (217938938171894814991/100000000000000000000)
  directionHi := (13621183635743425937/6250000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree020.table
  base := (-21586028419107979090326257327032455749/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-155408013147083990614880653650576000000000000)
      constant := (774193721744578941081594251776112141404942432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree020.table
  base := (-143663139050361669192929440516434173283/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-155790618325733160677663012322526000000000000)
      constant := (777764021977518741946264638597976774991700585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217938938171894814991/100000000000000000000)
  centralHi := (13621183635743425937/6250000000000000000)
  directionLo := (111800316320394464073/50000000000000000000)
  directionHi := (223600632640788928147/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree021.table
  base := (-309626591521350417258704159182898983839/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-163174898273662142889362534691161000000000000)
      constant := (845487601509586571727946940871455112329291805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree021.table
  base := (-196586284808425180498722431253789641119/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-163576633711243771455284011296708500000000000)
      constant := (849483244613449355081348283485463953717560648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111800316320394464073/50000000000000000000)
  centralHi := (223600632640788928147/100000000000000000000)
  directionLo := (14320154211922393019/6250000000000000000)
  directionHi := (45824493478151657661/20000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree022.table
  base := (-2310057652334133527886733319729324190571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-170941783400240295163844415731746000000000000)
      constant := (921657888861794082014533058797022663931985229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree022.table
  base := (-2331893025847557761257750920359032686691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-171362649096754382232905010270891000000000000)
      constant := (926095231312458568948732441527787382563065109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14320154211922393019/6250000000000000000)
  centralHi := (45824493478151657661/20000000000000000000)
  directionLo := (58628580492525756773/25000000000000000000)
  directionHi := (234514321970103027093/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree023.table
  base := (-2987463265474629644031223224397920509543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-178708668526818447438326296772331000000000000)
      constant := (1002593022891743085030080561138814687882151857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree023.table
  base := (-1503420604759813739811287741696397821971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-179148664482264993010526009245073500000000000)
      constant := (1007488614981575284343324317238867560386147658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58628580492525756773/25000000000000000000)
  centralHi := (234514321970103027093/100000000000000000000)
  directionLo := (59946241205644620201/25000000000000000000)
  directionHi := (47956992964515696161/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree024.table
  base := (-897400120059903400239782989523838372827/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-186475553653396599712808177812916000000000000)
      constant := (1088198637379994363105855372983997299035167092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree024.table
  base := (-1803383318219360615255135901842273264947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-186934679867775603788147008219256000000000000)
      constant := (1093569221958050417713947094221599940848551306) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59946241205644620201/25000000000000000000)
  centralHi := (47956992964515696161/20000000000000000000)
  directionLo := (122471110369786036779/50000000000000000000)
  directionHi := (244942220739572073559/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree025.table
  base := (-164972253247331438147374267542419962749/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-194242438779974751987290058853501000000000000)
      constant := (1178394786737060516380160729324466223999936275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree025.table
  base := (-1034871901149264763777319993356209400063/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-194720695253286214565768007193438500000000000)
      constant := (1184257297784065332420437495095548700389829348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122471110369786036779/50000000000000000000)
  centralHi := (244942220739572073559/100000000000000000000)
  directionLo := (124996553599190589637/50000000000000000000)
  directionHi := (9999724287935247171/4000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree026.table
  base := (-2299113271352570143253676058146335732051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-202009323906552904261771939894086000000000000)
      constant := (1273113677928342310799547691760427958394695498) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree026.table
  base := (-4611631419014653669290636639392559931969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-202506710638796825343389006167621000000000000)
      constant := (1279485237321110878748195075026922371133984231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124996553599190589637/50000000000000000000)
  centralHi := (9999724287935247171/4000000000000000000)
  directionLo := (127471973186823851669/50000000000000000000)
  directionHi := (254943946373647703339/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree027.table
  base := (-100339997918240905000576104584574342929/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-209776209033131056536253820934671000000000000)
      constant := (1372297789747768579259238652327938731389063550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree027.table
  base := (-1005763794707937891235171387505223055491/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-210292726024307436121010005141803500000000000)
      constant := (1379195701831041727804997258114013316804681545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127471973186823851669/50000000000000000000)
  centralHi := (254943946373647703339/100000000000000000000)
  directionLo := (259800457925765419727/100000000000000000000)
  directionHi := (16237528620360338733/6250000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree028.table
  base := (-1346353124172118628733984571551464373473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-217543094159709208810735701975256000000000000)
      constant := (1475898299129211805844553256764600047704807708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree028.table
  base := (-5395819214004015820865975967603888020833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-218078741409818046898631004115986000000000000)
      constant := (1483340043297427183809408385303982238299482567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259800457925765419727/100000000000000000000)
  centralHi := (16237528620360338733/6250000000000000000)
  directionLo := (264567836450891097823/100000000000000000000)
  directionHi := (8267744889090346807/3125000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree029.table
  base := (-2853763797204502746892407452374606703659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-225309979286287361085217583015841000000000000)
      constant := (1583873756865801926370007100108038149031949082) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree029.table
  base := (-2858339554933866478206787429336208265819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-225864756795328657676252003090168500000000000)
      constant := (1591876978584804764692099076499425397710760762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264567836450891097823/100000000000000000000)
  centralHi := (8267744889090346807/3125000000000000000)
  directionLo := (13462540829109257747/5000000000000000000)
  directionHi := (269250816582185154941/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree030.table
  base := (-5986795212701436051817780425276476476597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-233076864412865513359699464056426000000000000)
      constant := (1696188969266511774812263017540652163462234003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree030.table
  base := (-2997416695530328141763675993160239095111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-233650772180839268453873002064351000000000000)
      constant := (1704771470013160423346419899570961676981545378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13462540829109257747/5000000000000000000)
  centralHi := (269250816582185154941/100000000000000000000)
  directionLo := (136926864033360492127/50000000000000000000)
  directionHi := (54770745613344196851/20000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree031.table
  base := (-3113072466823533456187455798924595916319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-240843749539443665634181345097011000000000000)
      constant := (1812814051664530002492528886135064269115259762) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree031.table
  base := (-3116598697448131322055528636537519208889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-241436787566349879231494001038533500000000000)
      constant := (1821993778226559382508110701558893501850246622) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136926864033360492127/50000000000000000000)
  centralHi := (54770745613344196851/20000000000000000000)
  directionLo := (139190271321229215341/50000000000000000000)
  directionHi := (278380542642458430683/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree032.table
  base := (-6428064529370038999432736482983533489009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-248610634666021817908663226137596000000000000)
      constant := (1933723626296418247845320143145948974878619191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree032.table
  base := (-6434245723737874754584470492151423253079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-249222802951860490009115000012716000000000000)
      constant := (1943518659806293387146973308996651331395341121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139190271321229215341/50000000000000000000)
  centralHi := (278380542642458430683/100000000000000000000)
  directionLo := (70708728539948335741/25000000000000000000)
  directionHi := (56566982831958668593/20000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree033.table
  base := (-1648666663608758562294666089269745122909/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-256377519792599970183145107178181000000000000)
      constant := (2058896141972962190439589026544755195004821164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree033.table
  base := (-1650019733575737623260223949569351020079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-257008818337371100786735998986898500000000000)
      constant := (2069324686973287649448577926201857169726696484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70708728539948335741/25000000000000000000)
  centralHi := (56566982831958668593/20000000000000000000)
  directionLo := (287220213100759538113/100000000000000000000)
  directionHi := (143610106550379769057/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree034.table
  base := (-6727745440258607686035712139585791246289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-264144404919178122457626988218766000000000000)
      constant := (2188313296759581552471196340736170843496605911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree034.table
  base := (-3366240053419345273667858927780735569761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-264794833722881711564356997961081000000000000)
      constant := (2199393670525940475196111774215940307905736078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287220213100759538113/100000000000000000000)
  centralHi := (143610106550379769057/50000000000000000000)
  directionLo := (291539556423333012451/100000000000000000000)
  directionHi := (72884889105833253113/25000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree035.table
  base := (-3414412267607807059483249463505418222123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-271911290045756274732108869259351000000000000)
      constant := (2321959547919204440033914408316729332432246554) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree035.table
  base := (-3416481421979676404992327832647689311947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-272580849108392322341977996935263500000000000)
      constant := (2333710170203983819628022003506723561407657306) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291539556423333012451/100000000000000000000)
  centralHi := (72884889105833253113/25000000000000000000)
  directionLo := (18487239592632474863/6250000000000000000)
  directionHi := (295795833482119597809/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree036.table
  base := (-1379839578214575635380432127004977032323/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-279678175172334427006590750299936000000000000)
      constant := (2459821695849857475088016711810673146466365385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree036.table
  base := (-3451406002420458970303226995313890908579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-280366864493902933119598995909446000000000000)
      constant := (2472261079158963504035537798745327497683171242) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18487239592632474863/6250000000000000000)
  centralHi := (295795833482119597809/100000000000000000000)
  directionLo := (299991728638057415129/100000000000000000000)
  directionHi := (29999172863805741513/10000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree037.table
  base := (-867495549369682120728334509499529613731/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-287445060298912579281072631340521000000000000)
      constant := (2601888530803957548095360683353033262282640552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree037.table
  base := (-13886236556082422517114009463633845349/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-288152879879413543897219994883628500000000000)
      constant := (2615035271276901152335909706657217790547425500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299991728638057415129/100000000000000000000)
  centralHi := (29999172863805741513/10000000000000000000)
  directionLo := (2433037928478622689/800000000000000000)
  directionHi := (152064870529913918063/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree038.table
  base := (-6952057277589370986305193279142596688059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-295211945425490731555554512381106000000000000)
      constant := (2748150532894929729929681247897759871185110141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree038.table
  base := (-1738701881711891271627253393677696399509/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-295938895264924154674840993857811000000000000)
      constant := (2762023301826402687505553456541059151114434764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2433037928478622689/800000000000000000)
  centralHi := (152064870529913918063/50000000000000000000)
  directionLo := (30821220213188507337/10000000000000000000)
  directionHi := (308212202131885073371/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree039.table
  base := (-6936269086767168813629795708909688989787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-302978830552068883830036393421691000000000000)
      constant := (2898599617342681026574423862024042137615182813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree039.table
  base := (-6938665698559853951152169740500983354681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-303724910650434765452461992831993500000000000)
      constant := (2913217153359062089497707528651475937548899119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30821220213188507337/10000000000000000000)
  centralHi := (308212202131885073371/100000000000000000000)
  directionLo := (156120645406728665879/50000000000000000000)
  directionHi := (312241290813457331759/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree040.table
  base := (-6893272895413829547973845170709181154609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-310745715678647036104518274462276000000000000)
      constant := (3053228918130324128228720061954875643041833591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree040.table
  base := (-6895359968816371170053874455664762417021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-311510926035945376230082991806176000000000000)
      constant := (3068610020016193128179866863077173758583968779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156120645406728665879/50000000000000000000)
  centralHi := (312241290813457331759/100000000000000000000)
  directionLo := (316219047235807865511/100000000000000000000)
  directionHi := (39527380904475983189/12500000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree041.table
  base := (-170591007805261880299120991255241861939/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-318512600805225188379000155502861000000000000)
      constant := (3212032604277702909139746740738454985654410440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree041.table
  base := (-3412728345145285866919532063195450915117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-319296941421455987007703990780358500000000000)
      constant := (3228196124434173889192666483538620879179782966) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316219047235807865511/100000000000000000000)
  centralHi := (39527380904475983189/12500000000000000000)
  directionLo := (80036846194655144213/25000000000000000000)
  directionHi := (320147384778620576853/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree042.table
  base := (-1681964194254765140650348292294065269033/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-326279485931803340653482036543446000000000000)
      constant := (3375005723812785568831361036738754460762377468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree042.table
  base := (-84117957860804300994694278518840191257/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-327082956806966597785324989754541000000000000)
      constant := (3391970562320243228589577726238244771718987440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80036846194655144213/25000000000000000000)
  centralHi := (320147384778620576853/100000000000000000000)
  directionLo := (40503512603549697867/12500000000000000000)
  directionHi := (324028100828397582937/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree043.table
  base := (-3303167275251622561659160148634981631297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-334046371058381492927963917584031000000000000)
      constant := (3542144071264542116505004406530661979758278606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree043.table
  base := (-660770789728191962005438386687992840171/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-334868972192477208562945988728723500000000000)
      constant := (3559929170516297241728718835653264069124156290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40503512603549697867/12500000000000000000)
  centralHi := (324028100828397582937/100000000000000000000)
  directionLo := (327862886390524907373/100000000000000000000)
  directionHi := (163931443195262453687/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree044.table
  base := (-1614855936396904834477459774430216082543/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-341813256184959645202445798624616000000000000)
      constant := (3713444075131028805043532031651167462967915428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree044.table
  base := (-201894279196277613911043783297590003083/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-342654987577987819340566987702906000000000000)
      constant := (3732068415000773821068046249704754600113610144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327862886390524907373/100000000000000000000)
  centralHi := (163931443195262453687/50000000000000000000)
  directionLo := (331653334700850391851/100000000000000000000)
  directionHi := (82913333675212597963/25000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree045.table
  base := (-6287421695963580464831521666756903395097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-349580141311537797476927679665201000000000000)
      constant := (3888902702311259691013438621146649703466615503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree045.table
  base := (-3144228912291864551765414068486685708277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-350441002963498430118187986677088500000000000)
      constant := (3908385295815418816038297320711176356929732646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331653334700850391851/100000000000000000000)
  centralHi := (82913333675212597963/25000000000000000000)
  directionLo := (335400948961183392219/100000000000000000000)
  directionHi := (16770047448059169611/5000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree046.table
  base := (-3045290456167705519853720965899629406551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-357347026438115949751409560705786000000000000)
      constant := (4068517376943540388268822996883485260847546498) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree046.table
  base := (-6091480210483526645591641175559909052973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-358227018349009040895808985651271000000000000)
      constant := (4088877266359200612934690887534284242750622427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335400948961183392219/100000000000000000000)
  centralHi := (16770047448059169611/5000000000000000000)
  directionLo := (67821429861049198903/20000000000000000000)
  directionHi := (84776787326311498629/25000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree047.table
  base := (-18340986997820530493616134228174418829/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-365113911564694102025891441746371000000000000)
      constant := (4252285911478511818657710196084901556128118720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree047.table
  base := (-2934948003930561137513188238316077772593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-366013033734519651673429984625453500000000000)
      constant := (4273542164878218701673579789425216350033557614) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67821429861049198903/20000000000000000000)
  centralHi := (84776787326311498629/25000000000000000000)
  directionLo := (42846659885828332779/12500000000000000000)
  directionHi := (342773279086626662233/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree048.table
  base := (-2811604296838968005245000165194007010963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-372880796691272254300373322786956000000000000)
      constant := (4440206448142565799513434290315487868962332874) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree048.table
  base := (-5623885107305086213328878655608134052193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-373799049120030262451050983599636000000000000)
      constant := (4462378156308579077425505317462093424533579207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42846659885828332779/12500000000000000000)
  centralHi := (342773279086626662233/100000000000000000000)
  directionLo := (346400610567687226303/100000000000000000000)
  directionHi := (5412509540120112911/1562500000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree049.table
  base := (-5353013837785593714557829712663665662481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-380647681817850406574855203827541000000000000)
      constant := (4632277409225334350796108896082367821577031319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree049.table
  base := (-5353600213701917805408381366244382771639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-381585064505540873228671982573818500000000000)
      constant := (4655383682907734560373048379142945020096510561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346400610567687226303/100000000000000000000)
  centralHi := (5412509540120112911/1562500000000000000)
  directionLo := (43748793759716706373/12500000000000000000)
  directionHi := (69998070015546730197/20000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree050.table
  base := (-5058662918135189665101416172929602972247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-388414566944428558849337084868126000000000000)
      constant := (4828497454861072565550543268874982620080108353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree050.table
  base := (-1011834190897427437645038292083090155659/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-389371079891051484006292981548001000000000000)
      constant := (4852557422346215409599076884271798861610612705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43748793759716706373/12500000000000000000)
  centralHi := (69998070015546730197/20000000000000000000)
  directionLo := (176771821349870839353/50000000000000000000)
  directionHi := (353543642699741678707/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree051.table
  base := (-94805347604260038907095990300954634953/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-396181452071006711123818965908711000000000000)
      constant := (5028865447174274921049666968654136963442222350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree051.table
  base := (-948141473414762236776168274322638541737/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-397157095276562094783913980522183500000000000)
      constant := (5053898252132370930451333100494604539928704315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176771821349870839353/50000000000000000000)
  centralHi := (353543642699741678707/100000000000000000000)
  directionLo := (178530788268627954699/50000000000000000000)
  directionHi := (357061576537255909399/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree052.table
  base := (-2198960976718164443195161904487442769853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-403948337197584863398300846949296000000000000)
      constant := (5233380419830155557018211013562201192609459094) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree052.table
  base := (-4398302859274227971160807084048066193351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-404943110662072705561534979496366000000000000)
      constant := (5259405219413107971218026387296431176761626449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178530788268627954699/50000000000000000000)
  centralHi := (357061576537255909399/100000000000000000000)
  directionLo := (72109037321306325117/20000000000000000000)
  directionHi := (180272593303265812793/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree053.table
  base := (-62995423220950481534237279364084349951/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-411715222324163015672782727989881000000000000)
      constant := (5442041552175242402430016812791529309953590336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree053.table
  base := (-4032036722353441125923198727410300393403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-412729126047583316339155978470548500000000000)
      constant := (5469077515338231720371828163244308744436895997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72109037321306325117/20000000000000000000)
  centralHi := (180272593303265812793/50000000000000000000)
  directionLo := (363995458393379908449/100000000000000000000)
  directionHi := (7279909167867598169/2000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree054.table
  base := (-1820845549215306642573512395084140363907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-419482107450741167947264609030466000000000000)
      constant := (5654848147276153476626765658248818868295569386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree054.table
  base := (-1820988132159402501062761805215609308559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-420515141433093927116776977444731000000000000)
      constant := (5682914453298759156148017896281869013886779282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363995458393379908449/100000000000000000000)
  centralHi := (7279909167867598169/2000000000000000000)
  directionLo := (183706665554679055169/50000000000000000000)
  directionHi := (367413331109358110339/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree055.table
  base := (-1613966005247971781254089228925750440217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-427248992577319320221746490071051000000000000)
      constant := (5871799613268927863133628852850138714518692766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree055.table
  base := (-645635724166729266447712526289997987193/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-428301156818604537894397976418913500000000000)
      constant := (5900915450453788682548661150465154121413221035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183706665554679055169/50000000000000000000)
  centralHi := (367413331109358110339/100000000000000000000)
  directionLo := (14831988027111827107/4000000000000000000)
  directionHi := (92699925169448919419/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree056.table
  base := (-2790479095319937302727285969851667253167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-435015877703897472496228371111636000000000000)
      constant := (6092895447519864799179937025263895142350443433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree056.table
  base := (-1395346146235514322328385044477853199531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-436087172204115148672018975393096000000000000)
      constant := (6123080012048974478520606097495276839023168538) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14831988027111827107/4000000000000000000)
  centralHi := (92699925169448919419/25000000000000000000)
  directionLo := (374155422476557087379/100000000000000000000)
  directionHi := (18707771123827854369/5000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree057.table
  base := (-2329374197320985837851130565967415907769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-442782762830475624770710252152221000000000000)
      constant := (6318135223174052274787480939660902265324848431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree057.table
  base := (-2329558449661872174923107353295959450111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-443873187589625759449639974367278500000000000)
      constant := (6349407718104750726741078988433321386399417689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (374155422476557087379/100000000000000000000)
  centralHi := (18707771123827854369/5000000000000000000)
  directionLo := (15099252554453361293/4000000000000000000)
  directionHi := (188740656930667016163/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree058.table
  base := (-1844652852214793367304385945541506817133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-450549647957053777045192133192806000000000000)
      constant := (6547518577731654391417929499634164588958426267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree058.table
  base := (-115300752527653470942658423563621464773/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-451659202975136370227260973341461000000000000)
      constant := (6579898212116199349088609182722953834005610032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15099252554453361293/4000000000000000000)
  centralHi := (188740656930667016163/50000000000000000000)
  directionLo := (76155631298111376053/20000000000000000000)
  directionHi := (190389078245278440133/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree059.table
  base := (-1336345238061080258497098480661256041139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-458316533083631929319674014233391000000000000)
      constant := (6781045203346283941603332822142019402124341061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree059.table
  base := (-668241365400718742906751498801509444163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-459445218360646981004881972315643500000000000)
      constant := (6814551191460570037545515805411226823070186474) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76155631298111376053/20000000000000000000)
  centralHi := (190389078245278440133/50000000000000000000)
  directionLo := (384046698470661347453/100000000000000000000)
  directionHi := (192023349235330673727/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree060.table
  base := (-804476982942969108160443626312966962347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-466083418210210081594155895273976000000000000)
      constant := (7018714838585864991734436186368151424017098253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree060.table
  base := (-40229785146164655659589397199739644069/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-467231233746157591782502971289826000000000000)
      constant := (7053366399254398961758739866246986617817042620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (384046698470661347453/100000000000000000000)
  centralHi := (192023349235330673727/50000000000000000000)
  directionLo := (9682191408459758171/2500000000000000000)
  directionHi := (387287656338390326841/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree061.table
  base := (-124534925445471243017873277903668277439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-473850303336788233868637776314561000000000000)
      constant := (7260527261435522589117308334219618234803689522) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree061.table
  base := (-49834466560463783540520590805239072041/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-475017249131668202560123970264008500000000000)
      constant := (7296343617441168303126831703970999499880548795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9682191408459758171/2500000000000000000)
  centralHi := (387287656338390326841/100000000000000000000)
  directionLo := (390501716895010823019/100000000000000000000)
  directionHi := (19525085844750541151/5000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree062.table
  base := (41232209449324627929283130266736884587/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-481617188463366386143119657355146000000000000)
      constant := (7506482283355270126988049000543769363677375896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree062.table
  base := (65953846908741569710165503127427506051/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-482803264517178813337744969238191000000000000)
      constant := (7543482660923551715901086325900819314946131255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390501716895010823019/100000000000000000000)
  centralHi := (19525085844750541151/5000000000000000000)
  directionLo := (196844769452873215917/50000000000000000000)
  directionHi := (78737907781149286367/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree063.table
  base := (932289900834892558517138696572001919531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-489384073589944538417601538395731000000000000)
      constant := (7756579744233488606600125437684558866581135731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree063.table
  base := (23305339919645570548208805056957081877/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-490589279902689424115365968212373500000000000)
      constant := (7794783372582391434608010549005470736439091080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196844769452873215917/50000000000000000000)
  centralHi := (78737907781149286367/20000000000000000000)
  directionLo := (79370350935267329347/20000000000000000000)
  directionHi := (24803234667271040421/6250000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree064.table
  base := (1558213495840941264759584727505736120583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-497150958716522690692083419436316000000000000)
      constant := (8010819508101161209835259637616294014166067183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree064.table
  base := (311629535957229402194914388870807552581/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-498375295288200034892986967186556000000000000)
      constant := (8050245619048406955655767846438051539219393905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79370350935267329347/20000000000000000000)
  centralHi := (24803234667271040421/6250000000000000000)
  directionLo := (399988971517409886839/100000000000000000000)
  directionHi := (9999724287935247171/2500000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree065.table
  base := (220761714151605080272220527533989168847/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-504917843843100842966565300476901000000000000)
      constant := (8269201459492182578138830302773244110114082470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree065.table
  base := (1103780192869606740845956284910423549067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-506161310673710645670607966160738500000000000)
      constant := (8309869287112884710850648964069545429998064934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399988971517409886839/100000000000000000000)
  centralHi := (9999724287935247171/2500000000000000000)
  directionLo := (201550886553137859091/50000000000000000000)
  directionHi := (403101773106275718183/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree066.table
  base := (720122806411357975978751083558239262179/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-512684728969678995241047181517486000000000000)
      constant := (8531725500352349646182970983899819894853951916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree066.table
  base := (1440221147243251479258913870255507538729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-513947326059221256448228965134921000000000000)
      constant := (8573654280680787645062640366704303739805149058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201550886553137859091/50000000000000000000)
  centralHi := (403101773106275718183/100000000000000000000)
  directionLo := (101547680188696162681/25000000000000000000)
  directionHi := (16247628830191386029/4000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree067.table
  base := (1788413792782317316391672064573936189081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-520451614096257147515529062558071000000000000)
      constant := (8798391547414322360175088821052868321129630562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree067.table
  base := (1788392704984390990090928660553567074751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-521733341444731867225849964109103500000000000)
      constant := (8841600518184315517753322090501953594209069902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101547680188696162681/25000000000000000000)
  centralHi := (16247628830191386029/4000000000000000000)
  directionLo := (40925635459105518227/10000000000000000000)
  directionHi := (409256354591055182271/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree068.table
  base := (2148309644810451324680845596872685863013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-528218499222835299790010943598656000000000000)
      constant := (9069199529968310952691195407342262536977191226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree068.table
  base := (4296582944995115516650867215561465984807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-529519356830242478003470963083286000000000000)
      constant := (9113707930387333600681326134548712014511016207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40925635459105518227/10000000000000000000)
  centralHi := (409256354591055182271/100000000000000000000)
  directionLo := (206149597331056862241/50000000000000000000)
  directionHi := (412299194662113724483/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree069.table
  base := (2519930225789768687294059580954522283839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-535985384349413452064492824639241000000000000)
      constant := (9344149387968835263526280031907249038634883278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree069.table
  base := (629978642317276064870377067281824304287/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-537305372215753088781091962057468500000000000)
      constant := (9389976458521602457052192759970375336574253496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206149597331056862241/50000000000000000000)
  centralHi := (412299194662113724483/100000000000000000000)
  directionLo := (207659870981910945657/50000000000000000000)
  directionHi := (83063948392764378263/20000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree070.table
  base := (5806546073008906800646489137887554032147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-543752269475991604338974705679826000000000000)
      constant := (9623241070426894214568610261872268438681931547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree070.table
  base := (5806519100640746572675884163739112863807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-545091387601263699558712961031651000000000000)
      constant := (9670406052704667522524194828866254565323695207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207659870981910945657/50000000000000000000)
  centralHi := (83063948392764378263/20000000000000000000)
  directionLo := (83663695880773436131/20000000000000000000)
  directionHi := (26144904962741698791/6250000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree071.table
  base := (6596671909426389263141263777896381190657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-551519154602569756613456586720411000000000000)
      constant := (9906474534044520582219687220793374859525892057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree071.table
  base := (3298324340380096641882771144055720111971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-552877402986774310336333960005833500000000000)
      constant := (9954996670596844383341894253708729270474432342) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83663695880773436131/20000000000000000000)
  centralHi := (26144904962741698791/6250000000000000000)
  directionLo := (421295872703058536353/100000000000000000000)
  directionHi := (210647936351529268177/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree072.table
  base := (7410234356623342660654036162496297862393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-559286039729147908887938467760996000000000000)
      constant := (10193849742055182008402941739685368734494270993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree072.table
  base := (148204287120200857120080517713281385189/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-560663418372284921113954958980016000000000000)
      constant := (10243748276261167793877969563270557170515649450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (421295872703058536353/100000000000000000000)
  centralHi := (210647936351529268177/50000000000000000000)
  directionLo := (424252371239690014447/100000000000000000000)
  directionHi := (26515773202480625903/6250000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree073.table
  base := (4123615177063573287099237147335146866591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-567052924855726061162420348801581000000000000)
      constant := (10485366663238997292224294245846679541372189582) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree073.table
  base := (1649442627258156526611752086868321483767/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-568449433757795531891575957954198500000000000)
      constant := (10536660839195632625525172164852251206029535835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424252371239690014447/100000000000000000000)
  centralHi := (26515773202480625903/6250000000000000000)
  directionLo := (427188408841307171389/100000000000000000000)
  directionHi := (42718840884130717139/10000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree074.table
  base := (72861258425735409930269030516836283027/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-574819809982304213436902229842166000000000000)
      constant := (10781025271086414790231574564857846365394803375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree074.table
  base := (4553821241879095537448283779846360434807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-576235449143306142669196956928381000000000000)
      constant := (10833734333511689974353623605856033320590932414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427188408841307171389/100000000000000000000)
  centralHi := (42718840884130717139/10000000000000000000)
  directionLo := (430104404527826079817/100000000000000000000)
  directionHi := (215052202263913039909/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree075.table
  base := (9991512997299003220253373433083841919867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-582586695108882365711384110882751000000000000)
      constant := (11080825543087972388641448552442585146424563267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree075.table
  base := (2497875061115576184261675375571411567053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-584021464528816753446817955902563500000000000)
      constant := (11134968737236896263266277808789940096332030612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430104404527826079817/100000000000000000000)
  centralHi := (215052202263913039909/50000000000000000000)
  directionLo := (433000763209609032879/100000000000000000000)
  directionHi := (5412509540120112911/1250000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree076.table
  base := (10898795562778848091101629322513400115639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-590353580235460517985865991923336000000000000)
      constant := (11384767460131132292840434198480601194579633439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree076.table
  base := (10898784590317809270546156239333662438581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-591807479914327364224438954876746000000000000)
      constant := (11440364031722953200589363149215524190535964781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (433000763209609032879/100000000000000000000)
  centralHi := (5412509540120112911/1250000000000000000)
  directionLo := (217938938171894814991/50000000000000000000)
  directionHi := (435877876343789629983/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree077.table
  base := (11829503408847185149251377929757772823951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-598120465362038670260347872963921000000000000)
      constant := (11692851005988049081366141336711359915577124151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree077.table
  base := (11829493969844552252828188764506086787759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-599593495299837975002059953850928500000000000)
      constant := (11749920201143211751460276281725206310071929559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217938938171894814991/50000000000000000000)
  centralHi := (435877876343789629983/100000000000000000000)
  directionLo := (438736122551859200893/100000000000000000000)
  directionHi := (219368061275929600447/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree078.table
  base := (127836351848364332318320951851680004147/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-605887350488616822534829754004506000000000000)
      constant := (12005076166880562758776127751100372272230354700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree078.table
  base := (12783627066352816773145033193305647623063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-607379510685348585779680952825111000000000000)
      constant := (12063637232066120113672479246531229786402865663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438736122551859200893/100000000000000000000)
  centralHi := (219368061275929600447/50000000000000000000)
  directionLo := (88315173640254610063/20000000000000000000)
  directionHi := (110393967050318262579/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree079.table
  base := (137611897440062431378557910097058562053/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-613654235615194974809311635045091000000000000)
      constant := (12321442931110775022871114954851369314150265300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree079.table
  base := (172014784530603515347878616456572060911/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-615165526070859196557301951799293500000000000)
      constant := (12381515113093138812546971095099478296218248880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88315173640254610063/20000000000000000000)
  centralHi := (110393967050318262579/25000000000000000000)
  directionLo := (444397467953605829259/100000000000000000000)
  directionHi := (22219873397680291463/5000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree080.table
  base := (2952433222557786200194809103779472989617/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-621421120741773127083793516085676000000000000)
      constant := (12641951288747321930530482716722832019835415085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree080.table
  base := (14762160109901610688807759303583351575753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-622951541456369807334922950773476000000000000)
      constant := (12703553834551380402482446533360173769424256353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444397467953605829259/100000000000000000000)
  centralHi := (22219873397680291463/5000000000000000000)
  directionLo := (447201265281577856293/100000000000000000000)
  directionHi := (223600632640788928147/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree081.table
  base := (15786563464671711787436713576892389867149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-629188005868351279358275397126261000000000000)
      constant := (12966601231358946561624945806183953144034786949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree081.table
  base := (631462332162878090050592110735532694669/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-630737556841880418112543949747658500000000000)
      constant := (13029753388232703542996911816734811194207961725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447201265281577856293/100000000000000000000)
  centralHi := (223600632640788928147/50000000000000000000)
  directionLo := (224993796478543061347/50000000000000000000)
  directionHi := (89997518591417224539/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree082.table
  base := (16834381098016717239681356126044024931053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-636954890994929431632757278166846000000000000)
      constant := (13295392751788241022059109782407676598321671653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree082.table
  base := (16834376662196123538557181069236109280949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-638523572227391028890164948721841000000000000)
      constant := (13360113767172241010666219066839362425774960749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224993796478543061347/50000000000000000000)
  centralHi := (89997518591417224539/20000000000000000000)
  directionLo := (14148649172256343487/3125000000000000000)
  directionHi := (90551354702440598317/20000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree083.table
  base := (17905618417225158165038101937057363000977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-644721776121507583907239159207431000000000000)
      constant := (13628325843959502063278549288983965034972966377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree083.table
  base := (1790561460495928592120907083570507670649/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-646309587612901639667785947696023500000000000)
      constant := (13694634965460402136631085409472156206232904490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14148649172256343487/3125000000000000000)
  centralHi := (90551354702440598317/20000000000000000000)
  directionLo := (455509119674950447193/100000000000000000000)
  directionHi := (227754559837475223597/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree084.table
  base := (2375034364592685199096628684644526679211/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-652488661248085736181721040248016000000000000)
      constant := (13965400502715557489428807592356968533237051288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree084.table
  base := (19000271640851179812674740416649257807819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-654095602998412250445406946670206000000000000)
      constant := (14033316978083290762849157836059852578897561619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455509119674950447193/100000000000000000000)
  centralHi := (227754559837475223597/50000000000000000000)
  directionLo := (458244934781516576609/100000000000000000000)
  directionHi := (45824493478151657661/10000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree085.table
  base := (4023670033493874713029665261460214343517/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-660255546374663888456202921288601000000000000)
      constant := (14306616723679195801827001267836045107591084585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree085.table
  base := (10059173676443471832306847981049374825511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-661881618383922861223027945644388500000000000)
      constant := (14376159800787244316665814968838908563940075422) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (458244934781516576609/100000000000000000000)
  centralHi := (45824493478151657661/10000000000000000000)
  directionLo := (14405141036451636309/3125000000000000000)
  directionHi := (460964513166452361889/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree086.table
  base := (4251968761047200359162503145091553981493/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-668022431501242040730684802329186000000000000)
      constant := (14651974503135489938320058901583744210826050465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree086.table
  base := (21259841387335157123188758331657678423769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-669667633769433472000648944618571000000000000)
      constant := (14723163429963848579051563743398145852600867569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14405141036451636309/3125000000000000000)
  centralHi := (460964513166452361889/100000000000000000000)
  directionLo := (7244814695816712061/1562500000000000000)
  directionHi := (92733628106453914381/20000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree087.table
  base := (5606188880248926543501214440163293330083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-675789316627820193005166683369771000000000000)
      constant := (15001473837931865120118110185156168896040706732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree087.table
  base := (5606188361037438420579161173969172805877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-677453649154944082778269943592753500000000000)
      constant := (15074327862552333625577848591594351595921005108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7244814695816712061/1562500000000000000)
  centralHi := (92733628106453914381/20000000000000000000)
  directionLo := (93271218859950691051/20000000000000000000)
  directionHi := (58294511787469181907/12500000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree088.table
  base := (4722617010502179165007592559128956383463/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-683556201754398345279648564410356000000000000)
      constant := (15355114725393235682708469057067828420338530315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree088.table
  base := (23613083268848291909212637667815235388613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-685239664540454693555890942566936000000000000)
      constant := (15429653095956724071188832611363345216199241213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93271218859950691051/20000000000000000000)
  centralHi := (58294511787469181907/12500000000000000000)
  directionLo := (93805728788041210837/20000000000000000000)
  directionHi := (234514321970103027093/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree089.table
  base := (6206208044321861191884969194994467065977/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-691323086880976497554130445450941000000000000)
      constant := (15712897163249939046955160214050034109160125508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree089.table
  base := (12412415322808995103060641115796913781137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-693025679925965304333511941541118500000000000)
      constant := (15789139127975513730805812406088140103712757074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93805728788041210837/20000000000000000000)
  centralHi := (234514321970103027093/50000000000000000000)
  directionLo := (235843025645373198889/50000000000000000000)
  directionHi := (471686051290746397779/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree090.table
  base := (26059996706575451978297760913511109518023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-699089972007554649828612326491526000000000000)
      constant := (16074821149576537472520389487502544328193352623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree090.table
  base := (26059995391463965025334416069337414913667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-700811695311475915111132940515301000000000000)
      constant := (16152785956741971797358617011964092844534317067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235843025645373198889/50000000000000000000)
  centralHi := (471686051290746397779/100000000000000000000)
  directionLo := (474328570853711798267/100000000000000000000)
  directionHi := (118582142713427949567/25000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree091.table
  base := (13659289240137372132310210692172846685641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-706856857134132802103094207532111000000000000)
      constant := (16440886682739849092665514009350179293080447682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree091.table
  base := (27318577351242155182461004164065395664573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-708597710696986525888753939489483500000000000)
      constant := (16520593580673473702705273480782984319924309173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474328570853711798267/100000000000000000000)
  centralHi := (118582142713427949567/25000000000000000000)
  directionLo := (47695645008112925803/10000000000000000000)
  directionHi := (476956450081129258031/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree092.table
  base := (5720115472521742940912955474113304586667/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-714623742260710954377576088572696000000000000)
      constant := (16811093761354816740179792412128583100442950335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree092.table
  base := (286005763934432198271480040175026626591/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-716383726082497136666374938463666000000000000)
      constant := (16892561998428492660831330426019910161785479100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47695645008112925803/10000000000000000000)
  centralHi := (476956450081129258031/100000000000000000000)
  directionLo := (59946241205644620201/12500000000000000000)
  directionHi := (479569929645156961609/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree093.table
  base := (14952996619225326744331449857333667722579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-722390627387289106652057969613281000000000000)
      constant := (17185442384247032848296842350502034363876056758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree093.table
  base := (29905992406613905139012551842934008714191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-724169741468007747443995937437848500000000000)
      constant := (17268691208870094029515062254186588541643462391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59946241205644620201/12500000000000000000)
  centralHi := (479569929645156961609/100000000000000000000)
  directionLo := (96433848739066481399/20000000000000000000)
  directionHi := (120542310923833101749/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree094.table
  base := (31234826010204192050564684496007980899601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-730157512513867258926539850653866000000000000)
      constant := (17563932550420916861271326414376082913156829801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree094.table
  base := (31234825296319528551341080915528689189587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-731955756853518358221616936412031000000000000)
      constant := (17648981211034949611893423871123021033422976987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96433848739066481399/20000000000000000000)
  centralHi := (120542310923833101749/25000000000000000000)
  directionLo := (484754620103405411849/100000000000000000000)
  directionHi := (9695092402068108237/2000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree095.table
  base := (32587075595154312725775361039813588079541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-737924397640445411201021731694451000000000000)
      constant := (17946564259032692883907733448097350286999397741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree095.table
  base := (16293537491282895373177596390635672536417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-739741772239028968999237935386213500000000000)
      constant := (18033432004107037560625757834199796959837979634) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484754620103405411849/100000000000000000000)
  centralHi := (9695092402068108237/2000000000000000000)
  directionLo := (243663140348240276479/50000000000000000000)
  directionHi := (487326280696480552959/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree096.table
  base := (33962741923217971699043473281932432978483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-745691282767023563475503612735036000000000000)
      constant := (18333337509367443786246683348355424748813505083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree096.table
  base := (6792548279522097311291201914751514863349/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-747527787624539579776858934360396000000000000)
      constant := (18422043587395319640797387990301725015605115745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243663140348240276479/50000000000000000000)
  centralHi := (487326280696480552959/100000000000000000000)
  directionLo := (489884441479144147117/100000000000000000000)
  directionHi := (244942220739572073559/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree097.table
  base := (276264257304953747945417251158415450777/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-753458167893601715749985493775621000000000000)
      constant := (18724252300819627097018715506181541364712150656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree097.table
  base := (35361824484106178789857493431530952275491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-755313803010050190554479933334578500000000000)
      constant := (18814815960314794645614904967204088212912283691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489884441479144147117/100000000000000000000)
  centralHi := (244942220739572073559/50000000000000000000)
  directionLo := (492429312845205285023/100000000000000000000)
  directionHi := (15388416026412665157/3125000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree098.table
  base := (18392162290170834695265331472389128503899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-761225053020179868024467374816206000000000000)
      constant := (19119308632876530687275004839593496499736547398) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree098.table
  base := (2299020262095237885463198876146614903943/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-763099818395560801332100932308761000000000000)
      constant := (19211749122370417620969715300614844773161960688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492429312845205285023/100000000000000000000)
  centralHi := (15388416026412665157/3125000000000000000)
  directionLo := (123740274944909587547/25000000000000000000)
  directionHi := (494961099779638350189/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree099.table
  base := (19115120408301396039254863841927897082623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-768991938146758020298949255856791000000000000)
      constant := (19518506505104224943539898061207987831279674446) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree099.table
  base := (764604809696295152844622644396106268303/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-770885833781071412109721931282943500000000000)
      constant := (19612843073143451685572535484824031720897945150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123740274944909587547/25000000000000000000)
  centralHi := (494961099779638350189/100000000000000000000)
  directionLo := (497480002051275587777/100000000000000000000)
  directionHi := (248740001025637793889/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree100.table
  base := (2481223350489577511003523844364730648967/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-776758823273336172573431136897376000000000000)
      constant := (19921845917135634963831849224076283877601797872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree100.table
  base := (39699573323275363794440218301651362299637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-778671849166582022887342930257126000000000000)
      constant := (20018097812279884707671198960216483046818597037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497480002051275587777/100000000000000000000)
  centralHi := (248740001025637793889/50000000000000000000)
  directionLo := (499986214396762358549/100000000000000000000)
  directionHi := (9999724287935247171/2000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree101.table
  base := (20596161461804876623270826741228370403427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (126)
      previous := (63)
      next := (63)
      square := (757634017127069431252195390000000000000)
      linear := (-76906745260260202416225175761000000000000)
      constant := (1992875881644977263840486834196331740806854) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree101.table
  base := (10298080669895801107308956239348904991467/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (126)
      previous := (63)
      next := (63)
      square := (757634017127069431252195390000000000000)
      linear := (-77096153764541969774038224608500000000000)
      constant := (2002501062590000850785072468194364369965868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499986214396762358549/100000000000000000000)
  centralHi := (9999724287935247171/2000000000000000000)
  directionLo := (502479926696254471707/100000000000000000000)
  directionHi := (125619981674063617927/25000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree102.table
  base := (42708488738227092774232773379359584515753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-792292593526492477122394898978546000000000000)
      constant := (20740949359416340119255778986851188621645196353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree102.table
  base := (2135424426448962827094458575053514272941/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-794243879937603244442584928205491000000000000)
      constant := (20841089654493026805463273056549157856965422820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502479926696254471707/100000000000000000000)
  centralHi := (125619981674063617927/25000000000000000000)
  directionLo := (504961324141306211659/100000000000000000000)
  directionHi := (25248066207065310583/5000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree103.table
  base := (22124035514991191309687930413123226062679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-800059478653070629396876780019131000000000000)
      constant := (21156713389182025076787138264021297933130776958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree103.table
  base := (44248070850573832881103617840379724051937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-802029895323113855220205927179673500000000000)
      constant := (21258826757104073387834968360130316033803809337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504961324141306211659/100000000000000000000)
  centralHi := (25248066207065310583/5000000000000000000)
  directionLo := (507430587395369152701/100000000000000000000)
  directionHi := (253715293697684576351/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree104.table
  base := (22905534890283760159040058393865313275783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-807826363779648781671358661059716000000000000)
      constant := (21576618957770706987796733986187128121452524766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree104.table
  base := (45811069626757594071160454126151744846383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-809815910708624465997826926153856000000000000)
      constant := (21680724647134105555001903599622779949177952983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507430587395369152701/100000000000000000000)
  centralHi := (253715293697684576351/50000000000000000000)
  directionLo := (127471973186823851669/25000000000000000000)
  directionHi := (509887892747295406677/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree105.table
  base := (23698742487276679241762747558727785867163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-815593248906226933945840542100301000000000000)
      constant := (22000666065024993119791614862609696162261859526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree105.table
  base := (11849371210675436577455427528341125682127/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-817601926094135076775447925128038500000000000)
      constant := (22106783324431854781387449240557081761083510108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127471973186823851669/25000000000000000000)
  centralHi := (509887892747295406677/100000000000000000000)
  directionLo := (256166706129107201321/50000000000000000000)
  directionHi := (512333412258214402643/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree106.table
  base := (49007316598951813383527425166171842794437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-823360134032805086220322423140886000000000000)
      constant := (22428854710812392030619766088096008468346051837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree106.table
  base := (49007316485933938159128372514786123830097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-825387941479645687553068924102221000000000000)
      constant := (22537002788870090609972985388390169124190819497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256166706129107201321/50000000000000000000)
  centralHi := (512333412258214402643/100000000000000000000)
  directionLo := (25738365695106475043/5000000000000000000)
  directionHi := (514767313902129500861/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree107.table
  base := (25320282321422072523738093309721992605971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-831127019159383238494804304181471000000000000)
      constant := (22861184895021521653840997905718508968147020342) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree107.table
  base := (50640564545978408503536933387271824374271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-833173956865156298330689923076403500000000000)
      constant := (22971383040341949801618852718594022099191938471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25738365695106475043/5000000000000000000)
  centralHi := (514767313902129500861/100000000000000000000)
  directionLo := (129297440425139889019/25000000000000000000)
  directionHi := (517189761700559556077/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree108.table
  base := (26148614548532712926400311672529132351763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-838893904285961390769286185222056000000000000)
      constant := (23297656617558890562777461951772485358240668726) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree108.table
  base := (52297229014050668213441482675310696733607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-840959972250666909108310922050586000000000000)
      constant := (23409924078757821782713941342692373917379525007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129297440425139889019/25000000000000000000)
  centralHi := (517189761700559556077/100000000000000000000)
  directionLo := (103920183170306167891/20000000000000000000)
  directionHi := (16237528620360338733/3125000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree109.table
  base := (10795461990787343979263925709659497837437/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-846660789412539543043768066262641000000000000)
      constant := (23738269878346165932280807755845027562198474185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree109.table
  base := (53977309882798466982414682376289514837131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-848745987636177519885931921024768500000000000)
      constant := (23852625904042706247882385985720567059603573331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103920183170306167891/20000000000000000000)
  centralHi := (16237528620360338733/3125000000000000000)
  directionLo := (130500233213301597087/25000000000000000000)
  directionHi := (522000932853206388349/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree110.table
  base := (6960100900879721732090819742070298657097/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-854427674539117695318249947303226000000000000)
      constant := (24183024677317854758220386239507330432808371976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree110.table
  base := (13920201786520510931912372180864250962021/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-856532003021688130663552919998951000000000000)
      constant := (24299488516133971494318471994213971771254304884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130500233213301597087/25000000000000000000)
  centralHi := (522000932853206388349/100000000000000000000)
  directionLo := (524389965622422772053/100000000000000000000)
  directionHi := (262194982811211386027/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree111.table
  base := (1435193021275352642882015120664464025051/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-862194559665695847592731828343811000000000000)
      constant := (24631921014419335969523022433783311775781810040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree111.table
  base := (28703860399393858703184456435252365417761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-864318018407198741441173918973133500000000000)
      constant := (24750511914979452861704831304951395728003159922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524389965622422772053/100000000000000000000)
  centralHi := (262194982811211386027/50000000000000000000)
  directionLo := (263384081804194171409/50000000000000000000)
  directionHi := (526768163608388342819/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree112.table
  base := (59158050881413299679057452776470596780527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-869961444792273999867213709384396000000000000)
      constant := (25084958889605190472685095386649400557758155927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree112.table
  base := (59158050836669773587375198405284716257473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-872104033792709352218794917947316000000000000)
      constant := (25205696100535839817128815604772517390542482073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263384081804194171409/50000000000000000000)
  centralHi := (526768163608388342819/100000000000000000000)
  directionLo := (529135672901782195647/100000000000000000000)
  directionHi := (8267744889090346807/1562500000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree113.table
  base := (7616474661818262327635408819903777927283/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-877728329918852152141695590424981000000000000)
      constant := (25542138302837784155754345045758885384089711064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree113.table
  base := (60931797256216364803335434874692007301713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-879890049178219962996415916921498500000000000)
      constant := (25665041072767308004576161874145213135234774313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (529135672901782195647/100000000000000000000)
  centralHi := (8267744889090346807/1562500000000000000)
  directionLo := (10629852726789584137/2000000000000000000)
  directionHi := (531492636339479206851/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree114.table
  base := (62728960087368550270638174822582164026511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-885495215045430304416177471465566000000000000)
      constant := (26003459254086065661617157881035206155234438711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree114.table
  base := (31364480027267895059548766969454247287713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-887676064563730573774036915895681000000000000)
      constant := (26128546831644359182807383659914998428163920626) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10629852726789584137/2000000000000000000)
  centralHi := (531492636339479206851/100000000000000000000)
  directionLo := (66729899200639198143/12500000000000000000)
  directionHi := (106767838721022717029/20000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree115.table
  base := (64549539257382028052089693612474414487587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-893262100172008456690659352506151000000000000)
      constant := (26468921743324546500575507046075078377187874987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree115.table
  base := (6454953922926006890603097332207594409563/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-895462079949241184551657914869863500000000000)
      constant := (26596213377142837581429821004345843424469521630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66729899200639198143/12500000000000000000)
  centralHi := (106767838721022717029/20000000000000000000)
  directionLo := (536175481325681282267/100000000000000000000)
  directionHi := (134043870331420320567/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree116.table
  base := (66393534802548426995988438969833854666617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-901028985298586608965141233546736000000000000)
      constant := (26938525770532435963836039334307997151454160017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree116.table
  base := (66393534778463190301003600849179043517309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-903248095334751795329278913844046000000000000)
      constant := (27068040709243095963628662823100416922920069109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (536175481325681282267/100000000000000000000)
  centralHi := (134043870331420320567/25000000000000000000)
  directionLo := (538501633164370309881/100000000000000000000)
  directionHi := (269250816582185154941/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree117.table
  base := (68260946721218242367522438464007161869591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-908795870425164761239623114587321000000000000)
      constant := (27412271335692907453598937814968867933231697791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree117.table
  base := (34130473350295907902551365082789254591369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-911034110720262406106899912818228500000000000)
      constant := (27544028827929288723376500802675043590923110338) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538501633164370309881/100000000000000000000)
  centralHi := (269250816582185154941/50000000000000000000)
  directionLo := (270408889954898719189/50000000000000000000)
  directionHi := (540817779909797438379/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree118.table
  base := (8768971876508698059433388814518406989299/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-916562755551742913514104995627906000000000000)
      constant := (27890158438792476373124020531371871657582712792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree118.table
  base := (17537943748601637149586189666366418516487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-918820126105773016884520911792411000000000000)
      constant := (28024177733188772773712682212887869216146735548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270408889954898719189/50000000000000000000)
  centralHi := (540817779909797438379/100000000000000000000)
  directionLo := (271562024780909929193/50000000000000000000)
  directionHi := (543124049561819858387/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree119.table
  base := (36033009837028238398428494231971982394101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-924329640678321065788586876668491000000000000)
      constant := (28372187079820472715900516758094782259804448602) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree119.table
  base := (72066019658932168458652486421790790856649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-926606141491283627662141910766593500000000000)
      constant := (28508487425011599893151797537283059326278676449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271562024780909929193/50000000000000000000)
  centralHi := (543124049561819858387/100000000000000000000)
  directionLo := (545420567414081118513/100000000000000000000)
  directionHi := (272710283707040559257/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree120.table
  base := (74003680706365033940531601814430630521067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-932096525804899218063068757709076000000000000)
      constant := (28858357258768594037053198535638846861945404467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree120.table
  base := (37001840346707736677726774680287703554357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-934392156876794238439762909740776000000000000)
      constant := (28996957903390086667779978089941959727915991514) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545420567414081118513/100000000000000000000)
  centralHi := (272710283707040559257/50000000000000000000)
  directionLo := (547707456133441968509/100000000000000000000)
  directionHi := (54770745613344196851/10000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree121.table
  base := (75964758108376327753059066099538909537923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-939863410931477370337550638749661000000000000)
      constant := (29348668975630526650488907210545300291196352523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree121.table
  base := (75964758097289574358987342929102010926347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-942178172262304849217383908714958500000000000)
      constant := (29489589168318450263624735943822299082209665747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547707456133441968509/100000000000000000000)
  centralHi := (54770745613344196851/10000000000000000000)
  directionLo := (137496208959109648601/25000000000000000000)
  directionHi := (109996967167287718881/20000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree122.table
  base := (77949251879634929713372796258038406139099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-947630296058055522612032519790246000000000000)
      constant := (29843122230401624729864242548604531281024948899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree122.table
  base := (3897462593507183249964084212102160374919/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-949964187647815459995004907689141000000000000)
      constant := (29986381219792500043885884861310852634690974380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137496208959109648601/25000000000000000000)
  centralHi := (109996967167287718881/20000000000000000000)
  directionLo := (552252824162903093173/100000000000000000000)
  directionHi := (276126412081451546587/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree123.table
  base := (79957162019822270483028043794273764409989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-955397181184633674886514400830831000000000000)
      constant := (30341717023078638549357729670412359545746297789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree123.table
  base := (15991432402339486864197993978378318313703/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-957750203033326070772625906663323500000000000)
      constant := (30487334057809376556507934141047637344340421515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (552252824162903093173/100000000000000000000)
  centralHi := (276126412081451546587/50000000000000000000)
  directionLo := (277255768173436932133/50000000000000000000)
  directionHi := (554511536346873864267/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree124.table
  base := (5124280533045880447913643100556734975753/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-963164066311211827160996281871416000000000000)
      constant := (30844453353659484423173326674636446055802501648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree124.table
  base := (81988488521779418599193988112673936171499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-965536218418836681550246905637506000000000000)
      constant := (30992447682367330700032993104807960322885461299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277255768173436932133/50000000000000000000)
  centralHi := (554511536346873864267/100000000000000000000)
  directionLo := (139190271321229215341/25000000000000000000)
  directionHi := (111352217056983372273/20000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree125.table
  base := (10505403925782667370551193911297625841341/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-970930951437789979435478162912001000000000000)
      constant := (31351331222143050026112947206696473524660156328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree125.table
  base := (84043231400308693391599979401325803055173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-973322233804347292327867904611688500000000000)
      constant := (31501722093465536964225223111901061235715819773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139190271321229215341/25000000000000000000)
  centralHi := (111352217056983372273/20000000000000000000)
  directionLo := (279500790800986160183/50000000000000000000)
  directionHi := (559001581601972320367/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree126.table
  base := (86121390652374065415913894434515089574573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-978697836564368131709960043952586000000000000)
      constant := (31862350628529029731519153847735417928750219173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree126.table
  base := (43060695323639699088735128864299169762291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-981108249189857903105488903585871000000000000)
      constant := (32015157291103935565912579027142572536490260982) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (279500790800986160183/50000000000000000000)
  centralHi := (559001581601972320367/100000000000000000000)
  directionLo := (140308283428708907767/25000000000000000000)
  directionHi := (561233133714835631069/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree127.table
  base := (5513935391694233802722444437658616546023/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-986464721690946283984441924993171000000000000)
      constant := (32377511572817785412955032503549764633175689968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree127.table
  base := (88222966262747662712091481178252514071177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-988894264575368513883109902560053500000000000)
      constant := (32532753275283099084728740049644939864790076577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140308283428708907767/25000000000000000000)
  centralHi := (561233133714835631069/100000000000000000000)
  directionLo := (563455847893375424919/100000000000000000000)
  directionHi := (14086396197334385623/2500000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree128.table
  base := (22586989562637936509210677826923462481577/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-994231606817524436258923806033756000000000000)
      constant := (32896814055010228843854247276844920963098267908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree128.table
  base := (1806959164936411389558506280464916709819/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-996680279960879124660730901534236000000000000)
      constant := (33054510046004119869077297616656602767843180950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell065.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563455847893375424919/100000000000000000000)
  centralHi := (14086396197334385623/2500000000000000000)
  directionLo := (565669828319586685929/100000000000000000000)
  directionHi := (56566982831958668593/10000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree129.table
  base := (3699854664113585419029191534902174965547/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-1001998491944102588533405687074341000000000000)
      constant := (33420258075107722413466922081544137045588623675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 407
  qDenominator := 808
  table := BinomialMassData.Q407_808.Degree129.table
  base := (92496366599646841997256513137800907737001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7728624608713235268203645173390000000000000)
      linear := (-1004466295346389735438351900508418500000000000)
      constant := (33580427603268515047609078533051506028575147201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q407_808.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell065.Kernel129
