import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell094.Parameters
import ForestUnimodality.BinomialMassData.Q3493_6868.Batch000_049
import ForestUnimodality.BinomialMassData.Q3493_6868.Batch050_099
import ForestUnimodality.BinomialMassData.Q26_51.Batch000_049
import ForestUnimodality.BinomialMassData.Q26_51.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree000.table
  base := (38884326088690603852029425531/1000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1186630357985819783639414000000000000000)
      linear := (-29791244891839477847150786000000000000)
      constant := (388843260886906038520294255310000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree000.table
  base := (38884326088690603852029425531/1000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1186630357985819783639414000000000000000)
      linear := (-29791244891839477847150786000000000000)
      constant := (388843260886906038520294255310000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree001.table
  base := (54980857235351023037455649348794511435581/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-3646223754383514365307677071614954000000000000)
      constant := (649303393257153370233072521302025941194442218836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree001.table
  base := (219522436254443350147313218037529045548187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-3224430737342068548092165122386000000000000)
      constant := (571819522010532147054527245921849047470834387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49990387388164557157/100000000000000000000)
  directionHi := (24995193694082278579/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree002.table
  base := (129294363707479045148586773927356823897663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-7204620267405090576208425229681954000000000000)
      constant := (384880161406288900016109609768633984607637416007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree002.table
  base := (64433101413588634689992690224496853420107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-6371374446720462614303891050386000000000000)
      constant := (338468648422934892647553593888304631491396614) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49990387388164557157/100000000000000000000)
  centralHi := (24995193694082278579/50000000000000000000)
  directionLo := (70697083832627241041/100000000000000000000)
  directionHi := (35348541916313620521/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree003.table
  base := (15919737775257762929585348314591603288377/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-10763016780426666787109173387748954000000000000)
      constant := (242941974427266578302181917751181150234140307765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree003.table
  base := (79249171617922436492812418959514276148977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-1057590906233206297835068553154000000000000)
      constant := (23718340449820191369371473590711625807054353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70697083832627241041/100000000000000000000)
  centralHi := (35348541916313620521/50000000000000000000)
  directionLo := (10823236355793929969/12500000000000000000)
  directionHi := (86585890846351439753/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree004.table
  base := (25729871461123925217499905870566984682119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-14321413293448242998009921545815954000000000000)
      constant := (166364709619784425949860256284563968609047041182) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree004.table
  base := (51198872991664159499511613176039925167547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-12665261865477250746727342906386000000000000)
      constant := (146160875366199422228574895463823845360789747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10823236355793929969/12500000000000000000)
  centralHi := (86585890846351439753/100000000000000000000)
  directionLo := (49990387388164557157/50000000000000000000)
  directionHi := (19996154955265822863/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree005.table
  base := (3480962381555987199104151787848193764647/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-17879809806469819208910669703882954000000000000)
      constant := (125467295756722356120860807931827894574244095830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree005.table
  base := (34619799882042393121827180769720346564541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-15812205574855644812939068834386000000000000)
      constant := (110297668496785514591505203493222621414371141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49990387388164557157/50000000000000000000)
  centralHi := (19996154955265822863/20000000000000000000)
  directionLo := (111781904421484115601/100000000000000000000)
  directionHi := (55890952210742057801/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree006.table
  base := (4877579389760760735807281376785137408811/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-21438206319491395419811417861949954000000000000)
      constant := (104741503436722977361530322575674193792021060895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree006.table
  base := (12124231276731476730250813410764615391191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-2106572142692670986572310529154000000000000)
      constant := (10242789626428836343462826902245947696108398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111781904421484115601/100000000000000000000)
  centralHi := (55890952210742057801/50000000000000000000)
  directionLo := (122450941145066631487/100000000000000000000)
  directionHi := (1913295955391666117/1562500000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree007.table
  base := (17436633973029965827847710282888052336703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-24996602832512971630712166020016954000000000000)
      constant := (96056714431459577479866875580655145825258410567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree007.table
  base := (17331068435178111659812360456380341850281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-22106092993612432945362520690386000000000000)
      constant := (84660575312906616973821152478697269152580881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122450941145066631487/100000000000000000000)
  centralHi := (1913295955391666117/1562500000000000000)
  directionLo := (132262132972863151623/100000000000000000000)
  directionHi := (16532766621607893953/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree008.table
  base := (6247528283985744131023893200463012530387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-28554999345534547841612914178083954000000000000)
      constant := (95106424243514919447264166230403736295392160886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree008.table
  base := (12411872817804457628673762340644140092133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-25253036702990827011574246618386000000000000)
      constant := (83937682532820534592558638681903408379637933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132262132972863151623/100000000000000000000)
  centralHi := (16532766621607893953/12500000000000000000)
  directionLo := (141394167665254482083/100000000000000000000)
  directionHi := (35348541916313620521/25000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree009.table
  base := (1755612062508581247839490787288265484693/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-32113395858556124052513662336150954000000000000)
      constant := (99576075165235576596649410960672400022515508385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree009.table
  base := (1741965641840841588715488505117581411967/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-3155553379152135675309552505154000000000000)
      constant := (9776102641172322806981397608130905140292315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141394167665254482083/100000000000000000000)
  centralHi := (35348541916313620521/25000000000000000000)
  directionLo := (149971162164493671471/100000000000000000000)
  directionHi := (9373197635280854467/6250000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree010.table
  base := (5854374782088591757415414258015222954211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-35671792371577700263414410494217954000000000000)
      constant := (108194243601668963227584373970460505623856952779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree010.table
  base := (579648348317790889772821119537576896389/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-31546924121747615143997698474386000000000000)
      constant := (95687897646852949893268683141532375075077890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149971162164493671471/100000000000000000000)
  centralHi := (9373197635280854467/6250000000000000000)
  directionLo := (9880217828797242221/6250000000000000000)
  directionHi := (158083485260755875537/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree011.table
  base := (3479499889846238057147116741935685746067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-39230188884599276474315158652284954000000000000)
      constant := (120240121536532077167600639666059490355436915963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree011.table
  base := (68582963845034906649869479051628976899/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-34693867831126009210209424402386000000000000)
      constant := (106415366307847275256263574659260348445714950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9880217828797242221/6250000000000000000)
  centralHi := (158083485260755875537/100000000000000000000)
  directionLo := (165799358091056499001/100000000000000000000)
  directionHi := (82899679045528249501/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree012.table
  base := (60350509583101056932783982950285154633/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-42788585397620852685215906810351954000000000000)
      constant := (135287200395826589634297475124882278280921158425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree012.table
  base := (732126295816763950275702245280707804569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-4204534615611600364046794481154000000000000)
      constant := (13310433871925488539937020311420249111040882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165799358091056499001/100000000000000000000)
  centralHi := (82899679045528249501/50000000000000000000)
  directionLo := (34634356338540575901/20000000000000000000)
  directionHi := (86585890846351439753/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree013.table
  base := (-74060938841635641941312642482510903303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-46346981910642428896116654968418954000000000000)
      constant := (153069311348137936121694378031158843327184724066) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree013.table
  base := (-5870031331184238740191110121789984613/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-40987755249882797342632876258386000000000000)
      constant := (135590365649420397722406811787411176000690784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34634356338540575901/20000000000000000000)
  centralHi := (86585890846351439753/50000000000000000000)
  directionLo := (90121452504167821737/50000000000000000000)
  directionHi := (7209716200333425739/4000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree014.table
  base := (-310192544970407882633587600579658709877/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-49905378423664005107017403126485954000000000000)
      constant := (173410132837410190056092008601822303668287124735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree014.table
  base := (-1586572360028785903809911293928639611917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-44134698959261191408844602186386000000000000)
      constant := (153650145873426413984032725259795608369403883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90121452504167821737/50000000000000000000)
  centralHi := (7209716200333425739/4000000000000000000)
  directionLo := (187046902238616793951/100000000000000000000)
  directionHi := (5845215694956774811/3125000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree015.table
  base := (-342726437986286416766569420138861262263/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-53463774936685581317918151284552954000000000000)
      constant := (196185692703659335449230825702990079621570676744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree015.table
  base := (-346723452239510041013861649854916291743/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-5253515852071065052784036457154000000000000)
      constant := (19318267079593572374724251702595433533490184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187046902238616793951/100000000000000000000)
  centralHi := (5845215694956774811/3125000000000000000)
  directionLo := (96805968912409308909/50000000000000000000)
  directionHi := (193611937824818617819/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree016.table
  base := (-750368544166441126511307821617377212587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-57022171449707157528818899442619954000000000000)
      constant := (221304085728565576788337072874635504153608018785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree016.table
  base := (-94513705064049307220801694674683334413/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-50428586378017979541268054042386000000000000)
      constant := (196152348408355604916255371945821945887671480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96805968912409308909/50000000000000000000)
  centralHi := (193611937824818617819/100000000000000000000)
  directionLo := (49990387388164557157/25000000000000000000)
  directionHi := (199961549552658228629/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree017.table
  base := (-4605168771060297332644820478229708534447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (795678)
      previous := (397839)
      next := (397839)
      square := (12104816281813347612905662214000000000000000)
      linear := (-209621342431587313978268676818986000000000000)
      constant := (860533655448228618471340687193278243240106153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree017.table
  base := (-289431493322773079947133827485046153833/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (702)
      previous := (351)
      next := (351)
      square := (10679673221872378052754726000000000000000)
      linear := (-185382457049814441548372941074000000000000)
      constant := (762807704061498329499934354150153353848048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49990387388164557157/25000000000000000000)
  centralHi := (199961549552658228629/100000000000000000000)
  directionLo := (1030578237334737171/500000000000000000)
  directionHi := (206115647466947434201/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree018.table
  base := (-5196319794013520888129653742604003687/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-64138964475750309950620395758753954000000000000)
      constant := (278299388209923244859565348807389989703381357568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree018.table
  base := (-167001884440266831375352031753861325917/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-6302497088530529741521278433154000000000000)
      constant := (27412409346092480893340167398812290457919584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1030578237334737171/500000000000000000)
  centralHi := (206115647466947434201/100000000000000000000)
  directionLo := (53022812874470430781/25000000000000000000)
  directionHi := (339346002396610757/160000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree019.table
  base := (-739390117405867715562862607520299773607/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-67697360988771886161521143916820954000000000000)
      constant := (310073315201609829805480564589137884185813703816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree019.table
  base := (-5935684466947899580615642824898603196021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-59869417506153161739903231826386000000000000)
      constant := (274892371366701033715927864818922733087149379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53022812874470430781/25000000000000000000)
  centralHi := (339346002396610757/160000000000000000)
  directionLo := (217903046773459499229/100000000000000000000)
  directionHi := (21790304677345949923/10000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree020.table
  base := (-6400415083948532124463601989172088606383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-71255757501793462372421892074887954000000000000)
      constant := (343977747388416239628760476423343976472496947913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree020.table
  base := (-6418737252956689814936304240824874744249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-63016361215531555806114957754386000000000000)
      constant := (304959777018956902239954657114334500790208351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217903046773459499229/100000000000000000000)
  centralHi := (21790304677345949923/10000000000000000000)
  directionLo := (223563808842968231203/100000000000000000000)
  directionHi := (55890952210742057801/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree021.table
  base := (-6787747191591687567604902717421707791921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-74814154014815038583322640232954954000000000000)
      constant := (379980747271926279966124373633787176397423411031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree021.table
  base := (-136080748080418132026565283597616260887/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-7351478324989994430258520409154000000000000)
      constant := (37431751279855603849947165519898445030182850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223563808842968231203/100000000000000000000)
  centralHi := (55890952210742057801/25000000000000000000)
  directionLo := (229084734226429855111/100000000000000000000)
  directionHi := (28635591778303731889/12500000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree022.table
  base := (-7086212633625930793508912853709284938473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-78372550527836614794223388391021954000000000000)
      constant := (418055500887618698773760373696357910875022071903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree022.table
  base := (-7100666595567379301071117791578958921171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-69310248634288343938538409610386000000000000)
      constant := (370646703428146447775949135529295127846034229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229084734226429855111/100000000000000000000)
  centralHi := (28635591778303731889/12500000000000000000)
  directionLo := (117237850422562725697/50000000000000000000)
  directionHi := (46895140169025090279/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree023.table
  base := (-3651737552727991359882331826598670045433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-81930947040858191005124136549088954000000000000)
      constant := (458179414979371487766454347047055361348858944926) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree023.table
  base := (-7316275032844102486517457699766250387183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-72457192343666738004750135538386000000000000)
      constant := (406222704563444907736539501250335982742937017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117237850422562725697/50000000000000000000)
  centralHi := (46895140169025090279/20000000000000000000)
  directionLo := (239745475698774191353/100000000000000000000)
  directionHi := (119872737849387095677/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree024.table
  base := (-1861501573643080362430857949903768596311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-85489343553879767216024884707155954000000000000)
      constant := (500333410436482530842975531758620990970680401284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree024.table
  base := (-7457320970650972201898415268237877916251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-8400459561449459118995762385154000000000000)
      constant := (49288551889317920546694490462775253282203461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239745475698774191353/100000000000000000000)
  centralHi := (119872737849387095677/50000000000000000000)
  directionLo := (122450941145066631487/50000000000000000000)
  directionHi := (9796075291605330519/4000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree025.table
  base := (-117488730054763538783146809706792751329/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-89047740066901343426925632865222954000000000000)
      constant := (544501353775479120158214286009819195629743342016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree025.table
  base := (-7529263627896534127738477048031696205009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-78751079762423526137173587394386000000000000)
      constant := (482755291321014452012037684753969558170771591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122450941145066631487/50000000000000000000)
  centralHi := (9796075291605330519/4000000000000000000)
  directionLo := (49990387388164557157/20000000000000000000)
  directionHi := (124975968470411392893/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree026.table
  base := (-7527923868396488150989115805031471644403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-92606136579922919637826381023289954000000000000)
      constant := (590669590992490697251988789944399502791323604133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree026.table
  base := (-29440318184335912843907730273258305687/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-81898023471801920203385313322386000000000000)
      constant := (523685664924869865704070196913305317608476928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49990387388164557157/20000000000000000000)
  centralHi := (124975968470411392893/50000000000000000000)
  directionLo := (25490196078431372549/10000000000000000000)
  directionHi := (254901960784313725491/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree027.table
  base := (-7475863412838228832217005648524780799199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-96164533092944495848727129181356954000000000000)
      constant := (638826560615261029597402649145637547998470219289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree027.table
  base := (-7483603545227736278302321372367708692301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-9449440797908923807733004361154000000000000)
      constant := (62930880029480469731406347934093732187925011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25490196078431372549/10000000000000000000)
  centralHi := (254901960784313725491/100000000000000000000)
  directionLo := (259757672539054319257/100000000000000000000)
  directionHi := (129878836269527159629/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree028.table
  base := (-7366419059700550927434861385333683621403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-99722929605966072059627877339423954000000000000)
      constant := (688962469968096438563297479854577467986261651133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree028.table
  base := (-28801638976298411652526938149127448459/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-88191910890558708335808765178386000000000000)
      constant := (610823448864898773156555226830382593678884096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259757672539054319257/100000000000000000000)
  centralHi := (129878836269527159629/50000000000000000000)
  directionLo := (132262132972863151623/50000000000000000000)
  directionHi := (264524265945726303247/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree029.table
  base := (-3601202428322491833770769376517937747041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-103281326118987648270528625497490954000000000000)
      constant := (741069022988040494100881905358679572350527290702) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree029.table
  base := (-3604186122771423736314880770422505317193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-91338854599937102402020491106386000000000000)
      constant := (657014960921080169120369416181106127339962014) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132262132972863151623/50000000000000000000)
  centralHi := (264524265945726303247/100000000000000000000)
  directionLo := (134603237428882165077/50000000000000000000)
  directionHi := (53841294971552866031/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree030.table
  base := (-6986205056869661939218643777131359431493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-106839722632009224481429373655557954000000000000)
      constant := (795139190684466559930213636431833582704969233123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree030.table
  base := (-6991435178678028758195296850497401700657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-10498422034368388496470246337154000000000000)
      constant := (78327364735625397554990352084326250908510127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134603237428882165077/50000000000000000000)
  centralHi := (53841294971552866031/20000000000000000000)
  directionLo := (273808628309194924899/100000000000000000000)
  directionHi := (2738086283091949249/1000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree031.table
  base := (-839979988097095000348356252950522703741/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-110398119145030800692330121813624954000000000000)
      constant := (851167017197075274538358158861571158282807192408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree031.table
  base := (-3362209383471818500402904722017131966309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-97632742018693890534443942962386000000000000)
      constant := (754612184940179574701663423149382879511260582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273808628309194924899/100000000000000000000)
  centralHi := (2738086283091949249/1000000000000000000)
  directionLo := (139167348691944999679/50000000000000000000)
  directionHi := (278334697383889999359/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree032.table
  base := (-6405021283347269595735782773480402899407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-113956515658052376903230869971691954000000000000)
      constant := (909147455742481088974931420742777460496690116777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree032.table
  base := (-3204512908141162181061642115541029587221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-100779685728072284600655668890386000000000000)
      constant := (806008238881476320968137356602507564087276358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139167348691944999679/50000000000000000000)
  centralHi := (278334697383889999359/100000000000000000000)
  directionLo := (141394167665254482083/50000000000000000000)
  directionHi := (282788335330508964167/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree033.table
  base := (-1208639963774651441589866214405109101719/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-117514912171073953114131618129758954000000000000)
      constant := (969076229745269251233838117503884701067111675045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree033.table
  base := (-151167466106172210409416891563617654939/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-11547403270827853185207488313154000000000000)
      constant := (95458965886284887811529495399056579908905160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141394167665254482083/50000000000000000000)
  centralHi := (282788335330508964167/100000000000000000000)
  directionLo := (287172912076015878677/100000000000000000000)
  directionHi := (143586456038007939339/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree034.table
  base := (-5635604771660754706063144129180691229959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (795678)
      previous := (397839)
      next := (397839)
      square := (12104816281813347612905662214000000000000000)
      linear := (-418938784374032973443018568469986000000000000)
      constant := (3567300052721984125035986936682376768763188241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree034.table
  base := (-45109271574518040400463832102459035109/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (702)
      previous := (351)
      next := (351)
      square := (10679673221872378052754726000000000000000)
      linear := (-370496792895602327796121525074000000000000)
      constant := (3162547991675450858054609167500733585502375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287172912076015878677/100000000000000000000)
  centralHi := (143586456038007939339/50000000000000000000)
  directionLo := (291491544065068735737/100000000000000000000)
  directionHi := (145745772032534367869/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree035.table
  base := (-647909728302207162924795669699530434957/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-124631705197117105535933114445892954000000000000)
      constant := (1094764841237404757588073025972486900656304422616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree035.table
  base := (-648242694338322944975446438255810087069/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-110220516856207466799290846674386000000000000)
      constant := (970542577139695809159635911891033103708268248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291491544065068735737/100000000000000000000)
  centralHi := (145745772032534367869/50000000000000000000)
  directionLo := (36968390022054794329/12500000000000000000)
  directionHi := (295747120176438354633/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree036.table
  base := (-2343550859909554361450278166718497728801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-128190101710138681746833862603959954000000000000)
      constant := (1160519005361241399808821663636210655498393577422) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree036.table
  base := (-4689423020162765220998590434907040973447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-12596384507287317873944730289154000000000000)
      constant := (114314115077850918460227811549255865158673817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36968390022054794329/12500000000000000000)
  centralHi := (295747120176438354633/100000000000000000000)
  directionLo := (149971162164493671471/50000000000000000000)
  directionHi := (299942324328987342943/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree037.table
  base := (-4147824496451076544108966896073429432251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-131748498223160257957734610762026954000000000000)
      constant := (1228210002306147938222049850172678264998504581661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree037.table
  base := (-4149845828114643408163300560691633422231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-116514404274964254931714298530386000000000000)
      constant := (1088827814073786244807898016920373061468777169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149971162164493671471/50000000000000000000)
  centralHi := (299942324328987342943/100000000000000000000)
  directionLo := (304079655279820051529/100000000000000000000)
  directionHi := (30407965527982005153/10000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree038.table
  base := (-3566080061933992558824496220099380439599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-135306894736181834168635358920093954000000000000)
      constant := (1297835963261937739687099064535160564619203023689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree038.table
  base := (-3567838902660749040498500460413861069757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-119661347984342648997926024458386000000000000)
      constant := (1150543276427499466236337773723431547357562043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304079655279820051529/100000000000000000000)
  centralHi := (30407965527982005153/10000000000000000000)
  directionLo := (308161444029445313337/100000000000000000000)
  directionHi := (154080722014722656669/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree039.table
  base := (-58848111982340744455628261160692184561/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-138865291249203410379536107078160954000000000000)
      constant := (1369395304565762146643404122091310325415487303550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree039.table
  base := (-1471967488161845274092964261764642507899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-13645365743746782562681972265154000000000000)
      constant := (134885781902722958433385208089056036630434378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308161444029445313337/100000000000000000000)
  centralHi := (154080722014722656669/50000000000000000000)
  directionLo := (62437973835649637797/20000000000000000000)
  directionHi := (156094934589124094493/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree040.table
  base := (-17791065050342740558050845200251293889/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-142423687762224986590436855236227954000000000000)
      constant := (1442886684193134807172133356513828514496009200512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree040.table
  base := (-3645736483756954404162554087457588709/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-125955235403099437130349476314386000000000000)
      constant := (1279112922455118444886136308101016757354931875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62437973835649637797/20000000000000000000)
  centralHi := (156094934589124094493/50000000000000000000)
  directionLo := (316166970521511751073/100000000000000000000)
  directionHi := (158083485260755875537/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree041.table
  base := (-98188625266231060496350383334447056513/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-145982084275246562801337603394294954000000000000)
      constant := (1518308964888225390033212542972538484485786341488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree041.table
  base := (-98260757289355915371326404117782107017/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-129102179112477831196561202242386000000000000)
      constant := (1345964938223770135335895015381910379834380528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316166970521511751073/100000000000000000000)
  centralHi := (158083485260755875537/50000000000000000000)
  directionLo := (64018932224762775279/20000000000000000000)
  directionHi := (80023665280953469099/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree042.table
  base := (-82401753279915618898280410401937067997/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-149540480788268139012238351552361954000000000000)
      constant := (1595661182920048054336345267452852830511457922670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree042.table
  base := (-825019193568711222058188629614511877779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-14694346980206247251419214241154000000000000)
      constant := (157169693588138523198831149893809406067321869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64018932224762775279/20000000000000000000)
  centralHi := (80023665280953469099/25000000000000000000)
  directionLo := (64794947615130612007/20000000000000000000)
  directionHi := (80993684518913265009/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree043.table
  base := (-36531933086338282529230565503542997219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-153098877301289715223139099710428954000000000000)
      constant := (1674942521605968912124666161445066809928871635509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree043.table
  base := (-37400787426320123643527967208840439133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-135396066531234619328984654098386000000000000)
      constant := (1484799121328214851952002931809437806017815067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64794947615130612007/20000000000000000000)
  centralHi := (80993684518913265009/25000000000000000000)
  directionLo := (65561778420786227671/20000000000000000000)
  directionHi := (81952223025982784589/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree044.table
  base := (791204042488652109640103689617698999957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-156657273814311291434039847868495954000000000000)
      constant := (1756152288875048972194897582800698078627084232173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree044.table
  base := (790450793861227767175850002546698879551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-138543010240613013395196380026386000000000000)
      constant := (1556779971095732376279050672019007963785712151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65561778420786227671/20000000000000000000)
  centralHi := (81952223025982784589/25000000000000000000)
  directionLo := (331598716182112998003/100000000000000000000)
  directionHi := (82899679045528249501/25000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree045.table
  base := (829495730409506453163317095390384729781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-160215670327332867644940596026562954000000000000)
      constant := (1839289898254784335506280936788287305355270677018) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree045.table
  base := (207292346655115995656373048697456733649/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-15743328216665711940156456217154000000000000)
      constant := (181163253308742713011639013599768519968196488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331598716182112998003/100000000000000000000)
  centralHi := (82899679045528249501/25000000000000000000)
  directionLo := (83836428316113086701/25000000000000000000)
  directionHi := (67069142652890469361/20000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree046.table
  base := (2566661742770735334683751272723802663947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-163774066840354443855841344184629954000000000000)
      constant := (1924354852758884401269683634766382301671752847283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree046.table
  base := (2566096470302413824800879642862887552607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-144836897659369801527619831882386000000000000)
      constant := (1705866613841323610783427913517942370524330807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83836428316113086701/25000000000000000000)
  centralHi := (67069142652890469361/20000000000000000000)
  directionLo := (10595353226587366817/3125000000000000000)
  directionHi := (67810260650159147629/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree047.table
  base := (878518007941331540977429666917299739551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-167332463353376020066742092342696954000000000000)
      constant := (2011346731233441535954804616863046871587492672156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree047.table
  base := (1756791349083907645053354588644671723769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-147983841368748195593831557810386000000000000)
      constant := (1782971606056580617300156377431221582307046338) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10595353226587366817/3125000000000000000)
  centralHi := (67810260650159147629/20000000000000000000)
  directionLo := (85679207318375170749/25000000000000000000)
  directionHi := (342716829273500682997/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree048.table
  base := (4501101269020001662501177966051561638429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-170890859866397596277642840500763954000000000000)
      constant := (2100265176786389861453419878687983774299074512181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree048.table
  base := (2250338932197745612074679167194291841389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-16792309453125176628893698193154000000000000)
      constant := (206864882818279414228616644101230300684322842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85679207318375170749/25000000000000000000)
  centralHi := (342716829273500682997/100000000000000000000)
  directionLo := (34634356338540575901/10000000000000000000)
  directionHi := (346343563385405759011/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree049.table
  base := (221105874704959385257078631119655926197/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-174449256379419172488543588658830954000000000000)
      constant := (2191109886982386171523614836794286566495154688325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree049.table
  base := (5527280668223440413572010250113508785193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-154277728787504983726255009666386000000000000)
      constant := (1942303368281843977899667091294109236350286993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34634356338540575901/10000000000000000000)
  centralHi := (346343563385405759011/100000000000000000000)
  directionLo := (349932711717151900099/100000000000000000000)
  directionHi := (3499327117171519001/1000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree050.table
  base := (412101368380074373307104539932585522009/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-178007652892440748699444336816897954000000000000)
      constant := (2283880605533746926145579778246968382903903852816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree050.table
  base := (1648326325736636543686879410289473080671/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-157424672496883377792466735594386000000000000)
      constant := (2024529651625328358332394050496451677931301084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349932711717151900099/100000000000000000000)
  centralHi := (3499327117171519001/1000000000000000000)
  directionLo := (353485419163136205207/100000000000000000000)
  directionHi := (44185677395392025651/12500000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree051.table
  base := (7698952679890815620596163684775256395567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (795678)
      previous := (397839)
      next := (397839)
      square := (12104816281813347612905662214000000000000000)
      linear := (-628256226316478632907768460120986000000000000)
      constant := (8230370641035208526838361172905740890491178967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree051.table
  base := (769867908617121505429700744654928290709/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1186630357985819783639414000000000000000)
      linear := (-61734569860154468227096678786000000000000)
      constant := (810635373451773215218566791882549282907090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353485419163136205207/100000000000000000000)
  centralHi := (44185677395392025651/12500000000000000000)
  directionLo := (357002773647708320917/100000000000000000000)
  directionHi := (178501386823854160459/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree052.table
  base := (8843576797551334396426265068639420364997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-185124445918483901121245833133031954000000000000)
      constant := (2475199232116840636098929776174484978144423640733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree052.table
  base := (1768668090501361805970872990564406915493/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-163718559915640165924890187450386000000000000)
      constant := (2194102072318464251756787352494562111935986465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (357002773647708320917/100000000000000000000)
  centralHi := (178501386823854160459/50000000000000000000)
  directionLo := (360485810016671286949/100000000000000000000)
  directionHi := (7209716200333425739/2000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree053.table
  base := (2506860336346187041357800208328875956747/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-188682842431505477332146581291098954000000000000)
      constant := (2573746800147888053829776213762265019861801225932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree053.table
  base := (501361862663095873038726036265253088311/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-166865503625018559991101913378386000000000000)
      constant := (2281447913897788356175961605321026465653938220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360485810016671286949/100000000000000000000)
  centralHi := (7209716200333425739/2000000000000000000)
  directionLo := (9098387839838522279/2500000000000000000)
  directionHi := (363935513593540891161/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree054.table
  base := (1406312686757723889977246298472899119751/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-192241238944527053543047329449165954000000000000)
      constant := (2674219687191465031542795032413718756544380846712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree054.table
  base := (11250325316191396188208839800748852229589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-18890271926044106006368182145154000000000000)
      constant := (263388890688224980675983298291832418294351221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9098387839838522279/2500000000000000000)
  centralHi := (363935513593540891161/100000000000000000000)
  directionLo := (367352823435199894461/100000000000000000000)
  directionHi := (183676411717599947231/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree055.table
  base := (6256359627449069677375719624402968091887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-195799635457548629753948077607232954000000000000)
      constant := (2776617781253549189461704725345295826098086107886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree055.table
  base := (6256283612760674869876063613904707787791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-173159391043775348123525365234386000000000000)
      constant := (2461258281888745759356725678342512289912088782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367352823435199894461/100000000000000000000)
  centralHi := (183676411717599947231/50000000000000000000)
  directionLo := (9268465882935802459/2500000000000000000)
  directionHi := (370738635317432098361/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree056.table
  base := (431689451127628498051330703728136992607/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-199358031970570205964848825765299954000000000000)
      constant := (2880940987429820517135629846737178673068728896736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree056.table
  base := (13813931288562164847725147593995741940581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-176306334753153742189737091162386000000000000)
      constant := (2553722628549265471885355895161198924787451181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9268465882935802459/2500000000000000000)
  centralHi := (370738635317432098361/100000000000000000000)
  directionLo := (187046902238616793951/50000000000000000000)
  directionHi := (374093804477233587903/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree057.table
  base := (15154503758173206852425197422532681615313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-202916428483591782175749573923366954000000000000)
      constant := (2987189225298042855882527800911508766310606486857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree057.table
  base := (15154390660372300910220235717294699038857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-19939253162503570695105424121154000000000000)
      constant := (294210331816876779618242055327126168022229673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187046902238616793951/50000000000000000000)
  centralHi := (374093804477233587903/100000000000000000000)
  directionLo := (377419148135689367321/100000000000000000000)
  directionHi := (188709574067844683661/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree058.table
  base := (16534020104529936540089105649288489670129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-206474824996613358386650322081433954000000000000)
      constant := (3095362426708317407820043830306852711223120933481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree058.table
  base := (8266961301150046893110257824305044048087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-182600222171910530322160543018386000000000000)
      constant := (2743769296153389414962408592347722839138148574) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377419148135689367321/100000000000000000000)
  centralHi := (188709574067844683661/50000000000000000000)
  directionLo := (380715447822501939579/100000000000000000000)
  directionHi := (19035772391125096979/5000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree059.table
  base := (17952591886145003735859598205564689603647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-210033221509634934597551070239500954000000000000)
      constant := (3205460533910501342784165527859788848708926080583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree059.table
  base := (4488126963481964729000817746777191030389/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-185747165881288924388372268946386000000000000)
      constant := (2841351507857414269540207393013393895480167156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380715447822501939579/100000000000000000000)
  centralHi := (19035772391125096979/5000000000000000000)
  directionLo := (191991725760452342769/50000000000000000000)
  directionHi := (383983451520904685539/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree060.table
  base := (3882040500673548286761896513989807738923/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-213591618022656510808451818397567954000000000000)
      constant := (3317483497967347125532056002497059481536168840735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree060.table
  base := (9705065050537089970857478632008712397591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-20988234398963035383842666097154000000000000)
      constant := (326737731003419968483421981197541035765807598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191991725760452342769/50000000000000000000)
  centralHi := (383983451520904685539/100000000000000000000)
  directionLo := (96805968912409308909/25000000000000000000)
  directionHi := (387223875649637235637/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree061.table
  base := (20906837889768243022328361973316014787917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-217150014535678087019352566555634954000000000000)
      constant := (3431431277409767479110999371217970118220095440613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree061.table
  base := (836271021006516691985031687157424669397/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-192041053300045712520795720802386000000000000)
      constant := (3041633473731369216388918741877807539127539925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96805968912409308909/25000000000000000000)
  centralHi := (387223875649637235637/100000000000000000000)
  directionLo := (97609351724215083943/25000000000000000000)
  directionHi := (390437406896860335773/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree062.table
  base := (4488497225119574509820741263550338070137/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-220708411048699663230253314713701954000000000000)
      constant := (3547303837097282567104978539478691786054260590965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree062.table
  base := (5610608105378604788319012643617705447127/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-195187997009424106587007446730386000000000000)
      constant := (3144333161515310995227938381178830607471909308) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97609351724215083943/25000000000000000000)
  centralHi := (390437406896860335773/100000000000000000000)
  directionLo := (384399124921199663/97656250000000000)
  directionHi := (393624703919308454913/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree063.table
  base := (6004284277557213349465227483554735901409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-224266807561721239441154062871768954000000000000)
      constant := (3665101147252342748177097121326998505735395829604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree063.table
  base := (960683635040708513671143685430533296577/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-22037215635422500072579908073154000000000000)
      constant := (360970957399555823664098810746887603067768825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (384399124921199663/97656250000000000)
  centralHi := (393624703919308454913/100000000000000000000)
  directionLo := (396786398918589454869/100000000000000000000)
  directionHi := (39678639891858945487/10000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree064.table
  base := (12815391142286955977492236954303021687909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-227825204074742815652054811029835954000000000000)
      constant := (3784823182641996980947065014184685537809771911802) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree064.table
  base := (6407685622813664325753050635594847195823/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-201481884428180894719430898586386000000000000)
      constant := (3354849817131758884733194210059832790225342492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396786398918589454869/100000000000000000000)
  centralHi := (39678639891858945487/10000000000000000000)
  directionLo := (399923099105316457257/100000000000000000000)
  directionHi := (199961549552658228629/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree065.table
  base := (6820853598965003121555941402399860788563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-231383600587764391862955559187902954000000000000)
      constant := (3906469921884424859270131004748336360269175624428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree065.table
  base := (13641690077256332957080077690050622019309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-204628828137559288785642624514386000000000000)
      constant := (3462666744622414972690906815788983335744445418) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399923099105316457257/100000000000000000000)
  centralHi := (199961549552658228629/50000000000000000000)
  directionLo := (80607077612135159443/20000000000000000000)
  directionHi := (12594855876896118663/3125000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree066.table
  base := (28975027298293780398895187934270038000431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-234941997100785968073856307345969954000000000000)
      constant := (4030041346861280539236725099918373811058652626359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree066.table
  base := (5794999568255875225569010339444455558721/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-23086196871881964761317150049154000000000000)
      constant := (396909931488690446873810944359561238282351845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80607077612135159443/20000000000000000000)
  centralHi := (12594855876896118663/3125000000000000000)
  directionLo := (406123827004078022199/100000000000000000000)
  directionHi := (2030619135020390111/500000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree067.table
  base := (30705615784142238104604977577287146148989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-238500393613807544284757055504036954000000000000)
      constant := (4155537442219703714681257118425748865903226832021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree067.table
  base := (3838198806099061354188426562415937751143/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-210922715556316076918066076370386000000000000)
      constant := (3683417720186871297468804055536562832725783544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406123827004078022199/100000000000000000000)
  centralHi := (2030619135020390111/500000000000000000)
  directionLo := (51148619496836290313/12500000000000000000)
  directionHi := (81837791194938064501/20000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree068.table
  base := (1299007017623522340222349850572576204853/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (795678)
      previous := (397839)
      next := (397839)
      square := (12104816281813347612905662214000000000000000)
      linear := (-837573668258924292372518351771986000000000000)
      constant := (14819924550001093995077223183173569246642636325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree068.table
  base := (32475153655048004709072943138372854228527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (702)
      previous := (351)
      next := (351)
      square := (10679673221872378052754726000000000000000)
      linear := (-740725464587178100291618693074000000000000)
      constant := (13136165203276312739313869357477355688056743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51148619496836290313/12500000000000000000)
  centralHi := (81837791194938064501/20000000000000000000)
  directionLo := (1030578237334737171/250000000000000000)
  directionHi := (412231294933894868401/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree069.table
  base := (34283702528426630430001389549135645568889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-245617186639850696706558551820170954000000000000)
      constant := (4412303594029609905980177910340870769709540403121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree069.table
  base := (2142730237460817300736953502946620194133/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-24135178108341429450054392025154000000000000)
      constant := (434554604950750357238990811944101171777670992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1030578237334737171/250000000000000000)
  centralHi := (412231294933894868401/100000000000000000000)
  directionLo := (103812836198761621099/25000000000000000000)
  directionHi := (415251344795046484397/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree070.table
  base := (18065596939636140249901098036853560875501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-249175583152872272917459299978237954000000000000)
      constant := (4543573630116901987446178358920052809855789735178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree070.table
  base := (36131177781265332764440911518389463382821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-220363546684451259116701254154386000000000000)
      constant := (4027336814552161122181278280415850994258717421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103812836198761621099/25000000000000000000)
  centralHi := (415251344795046484397/100000000000000000000)
  directionLo := (418249588386304740213/100000000000000000000)
  directionHi := (209124794193152370107/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree071.table
  base := (1900882340422474564992967296763232192087/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-252733979665893849128360048136304954000000000000)
      constant := (4676768295297530047514548736539387455098751434860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree071.table
  base := (19008816487352410662972958212707903987131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-223510490393829653182912980082386000000000000)
      constant := (4145387846902800209574752504945262516541055462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418249588386304740213/100000000000000000000)
  centralHi := (209124794193152370107/50000000000000000000)
  directionLo := (10530662283794527061/2500000000000000000)
  directionHi := (421226491351781082441/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree072.table
  base := (4992882380146983196027211192009006715929/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-256292376178915425339260796294371954000000000000)
      constant := (4811887582865233123423688948176434312801251277448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree072.table
  base := (3994304715557214094561050781602576593403/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-25184159344800894138791634001154000000000000)
      constant := (473904948424859545988664477960719446354934670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10530662283794527061/2500000000000000000)
  centralHi := (421226491351781082441/100000000000000000000)
  directionLo := (424182502995763446249/100000000000000000000)
  directionHi := (339346002396610757/80000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree073.table
  base := (41907428650008748282199358720737753979993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-259850772691937001550161544452438954000000000000)
      constant := (4948931487137738725770447620178833123893123583377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree073.table
  base := (41907418440168191658189522918288915906569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-229804377812586441315336431938386000000000000)
      constant := (4386606876415466876141359002149697470272985969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424182502995763446249/100000000000000000000)
  centralHi := (339346002396610757/80000000000000000)
  directionLo := (106779514268588062779/25000000000000000000)
  directionHi := (427118057074352251117/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree074.table
  base := (4391075400183686463593015201097321673559/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-263409169204958577761062292610505954000000000000)
      constant := (5087900003300489469523649883784657740552808787510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree074.table
  base := (43910745233137591309835354471442484821423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-232951321521964835381548157866386000000000000)
      constant := (4509774864528473747322730979969685903020521223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106779514268588062779/25000000000000000000)
  centralHi := (427118057074352251117/100000000000000000000)
  directionLo := (215016786269228517809/50000000000000000000)
  directionHi := (430033572538457035619/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree075.table
  base := (45953033712960563039450177893547706423787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-266967565717980153971963040768572954000000000000)
      constant := (5228793127274215632527102472382559276783195793043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree075.table
  base := (22976513091678744449960991193280244561159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-26233140581260358827528875977154000000000000)
      constant := (514960944072053999109940884095015981356349902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215016786269228517809/50000000000000000000)
  centralHi := (430033572538457035619/100000000000000000000)
  directionLo := (216464727115878599381/50000000000000000000)
  directionHi := (432929454231757198763/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree076.table
  base := (4803426661102647239998186194693516842057/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-270525962231001730182863788926639954000000000000)
      constant := (5371610855602715137349269839373755407733829790730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree076.table
  base := (48034260146573483220287295594851872123983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-239245208940721623513971609722386000000000000)
      constant := (4761227769799297912599140281916145719394479783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216464727115878599381/50000000000000000000)
  centralHi := (432929454231757198763/100000000000000000000)
  directionLo := (217903046773459499229/50000000000000000000)
  directionHi := (435806093546918998459/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree077.table
  base := (50154451702770696885817480461775896847473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-274084358744023306393764537084706954000000000000)
      constant := (5516353185357757618591548593275643587461169829097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree077.table
  base := (10030889230750137319729372988034047231849/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-242392152650100017580183335650386000000000000)
      constant := (4889512681460449766316136154917554784250196245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217903046773459499229/50000000000000000000)
  centralHi := (435806093546918998459/100000000000000000000)
  directionLo := (109665967260770067013/25000000000000000000)
  directionHi := (438663869043080268053/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree078.table
  base := (1046271762933685049550351828910191411017/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-277642755257044882604665285242773954000000000000)
      constant := (5663020114058499697065053528983818651335684825650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree078.table
  base := (13078395846066451742347520531008719901593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-27282121817719823516266117953154000000000000)
      constant := (557722581055277818941978042630558080206241508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109665967260770067013/25000000000000000000)
  centralHi := (438663869043080268053/100000000000000000000)
  directionLo := (220751573513680439371/50000000000000000000)
  directionHi := (441503147027360878743/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree079.table
  base := (27255837614924840947476202980205731859709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-281201151770066458815566033400840954000000000000)
      constant := (5811611639603197259054264097158652650165115292202) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree079.table
  base := (10902334228639963058618167276988662093901/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-248686040068856805712606787506386000000000000)
      constant := (5151199412102965330552591654097881550531182505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220751573513680439371/50000000000000000000)
  centralHi := (441503147027360878743/100000000000000000000)
  directionLo := (55540535262865979709/12500000000000000000)
  directionHi := (444324282102927837673/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree080.table
  base := (1418717808707809576581391644454443149069/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-284759548283088035026466781558907954000000000000)
      constant := (5962127760211338385682889905446123513955827165640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree080.table
  base := (14187177210526002876186015266722710089087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-251832983778235199778818513434386000000000000)
      constant := (5284601227746289577671425787813863075766861148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55540535262865979709/12500000000000000000)
  centralHi := (444324282102927837673/100000000000000000000)
  directionLo := (223563808842968231203/50000000000000000000)
  directionHi := (447127617685936462407/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree081.table
  base := (59024698990447299412611766715786387576743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-288317944796109611237367529716974954000000000000)
      constant := (6114568474374606875553079839125910187064732694127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree081.table
  base := (14756173995677057002477960839878308388353/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-28331103054179288205003359929154000000000000)
      constant := (602189852792385822880130197067023324496936068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223563808842968231203/50000000000000000000)
  centralHi := (447127617685936462407/100000000000000000000)
  directionLo := (224956743246740507207/50000000000000000000)
  directionHi := (89982697298696202883/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree082.table
  base := (61339634722863915905860638749831259063937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-291876341309131187448268277875041954000000000000)
      constant := (6268933780815328918579447704522779139702542966393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree082.table
  base := (12267926428624232857687873075807254574407/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-258126871196991987911241965290386000000000000)
      constant := (5556521753161174542648906930150225345740163035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224956743246740507207/50000000000000000000)
  centralHi := (89982697298696202883/20000000000000000000)
  directionLo := (3621457688036139827/800000000000000000)
  directionHi := (56585276375564684797/12500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree083.table
  base := (63693519178462243599061279260411327895543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-295434737822152763659169026033108954000000000000)
      constant := (6425223678451261075456239415164029015744243467327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree083.table
  base := (31846758483070836640366273806708257891849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-261273814906370381977453691218386000000000000)
      constant := (5695040460906315804352627056644084357553398498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3621457688036139827/800000000000000000)
  centralHi := (56585276375564684797/12500000000000000000)
  directionLo := (45543410389556604571/10000000000000000000)
  directionHi := (455434103895566045711/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree084.table
  base := (66086352046311573652323213090887727480201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-298993134335174339870069774191175954000000000000)
      constant := (6583438166365751943690371100035599495619378285889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree084.table
  base := (33043175074679060305998729608000377854933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-29380084290638752893740601905154000000000000)
      constant := (648362755286702614447054793216960218400151274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45543410389556604571/10000000000000000000)
  centralHi := (455434103895566045711/100000000000000000000)
  directionLo := (229084734226429855111/50000000000000000000)
  directionHi := (458169468452859710223/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree085.table
  base := (34259066531536931293490227643453965163819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (795678)
      previous := (397839)
      next := (397839)
      square := (12104816281813347612905662214000000000000000)
      linear := (-1046891110201369951837268243422986000000000000)
      constant := (23334177314126150636750400810447745297272235238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree085.table
  base := (68518131436762321349305031215944468237927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (702)
      previous := (351)
      next := (351)
      square := (10679673221872378052754726000000000000000)
      linear := (-925839800432965986539367277074000000000000)
      constant := (20682334818399032632010230687483500214141343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229084734226429855111/50000000000000000000)
  centralHi := (458169468452859710223/100000000000000000000)
  directionLo := (46088859896247680043/10000000000000000000)
  directionHi := (460888598962476800431/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree086.table
  base := (8873607750717006259359442516657994772101/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-306109927361217492291871270507309954000000000000)
      constant := (6905640910043915496437946202772543928197507719912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree086.table
  base := (70988860611646389642239773786365154479781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-270714646034505564176088869002386000000000000)
      constant := (6120830355153649295138086956794631766801910381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46088859896247680043/10000000000000000000)
  centralHi := (460888598962476800431/100000000000000000000)
  directionLo := (463591781079878003973/100000000000000000000)
  directionHi := (231795890539939001987/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree087.table
  base := (73498538685451574566026502509955459445591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-309668323874239068502772018665376954000000000000)
      constant := (7069629164593389360148287424126379390981492925599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree087.table
  base := (36749268745293134725454900952146302183323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-30429065527098217582477843881154000000000000)
      constant := (696241286112469350413902801149288562661960694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463591781079878003973/100000000000000000000)
  centralHi := (231795890539939001987/50000000000000000000)
  directionLo := (466279292180161369077/100000000000000000000)
  directionHi := (233139646090080684539/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree088.table
  base := (76047162942321828637571654365538414498539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-313226720387260644713672766823443954000000000000)
      constant := (7235542006959483799493232607215011230860583341971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree088.table
  base := (76047161918345728119397594706149163049379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-277008533453262352308512320858386000000000000)
      constant := (6413218421689275565274029957563461973091434779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466279292180161369077/100000000000000000000)
  centralHi := (233139646090080684539/50000000000000000000)
  directionLo := (468951401690250902789/100000000000000000000)
  directionHi := (46895140169025090279/10000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree089.table
  base := (78634734640974122353174755580249974174963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-316785116900282220924573514981510954000000000000)
      constant := (7403379436743108076371058182240007909615492495707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree089.table
  base := (4914670860222501103577287019824545387917/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-280155477162640746374724046786386000000000000)
      constant := (6561970894843123820261597676220022280863553872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468951401690250902789/100000000000000000000)
  centralHi := (46895140169025090279/10000000000000000000)
  directionLo := (471608371404144838787/100000000000000000000)
  directionHi := (117902092851036209697/25000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree090.table
  base := (2031531341670365217031430877045672120143/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-320343513413303797135474263139577954000000000000)
      constant := (7573141453606429330880284711187511924000010269080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree090.table
  base := (81261252915079943328498020609538982408523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-31478046763557682271215085857154000000000000)
      constant := (745825443798296651464408624978516765916063147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471608371404144838787/100000000000000000000)
  centralHi := (117902092851036209697/25000000000000000000)
  directionLo := (474250455782267626609/100000000000000000000)
  directionHi := (47425045578226762661/10000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree091.table
  base := (83926719922853171397345162415036958626733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-323901909926325373346375011297644954000000000000)
      constant := (7744828057263512068270819068895688268820926663237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree091.table
  base := (83926719278875320221210721706643411557659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-286449364581397534507147498642386000000000000)
      constant := (6864592719469341183072232821686455513461471059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474250455782267626609/100000000000000000000)
  centralHi := (47425045578226762661/10000000000000000000)
  directionLo := (476877902235894490319/100000000000000000000)
  directionHi := (5960973777948681129/1250000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree092.table
  base := (43315566663506496207410065639623122256307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-327460306439346949557275759455711954000000000000)
      constant := (7918439247472386523986500484552107299738947694646) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree092.table
  base := (86631132775412249626866244003492117527069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-289596308290775928573359224570386000000000000)
      constant := (7018462070490270109398432784234794997687906469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476877902235894490319/100000000000000000000)
  centralHi := (5960973777948681129/1250000000000000000)
  directionLo := (479490951397548382707/100000000000000000000)
  directionHi := (119872737849387095677/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree093.table
  base := (89374493809850833930918754498545288597873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-331018702952368525768176507613778954000000000000)
      constant := (8093975024028327852536618046820729290817214814697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree093.table
  base := (89374493337431735003564807953575251433543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-32527028000017146959952327833154000000000000)
      constant := (797115227452501776905866242872355247664293927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479490951397548382707/100000000000000000000)
  centralHi := (119872737849387095677/25000000000000000000)
  directionLo := (48208983737820575153/10000000000000000000)
  directionHi := (482089837378205751531/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree094.table
  base := (23039200328156339260359022124756780269303/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-334577099465390101979077255771845954000000000000)
      constant := (8271435386758161358852413107805698417349396847868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree094.table
  base := (92156800908068243468392430204650270094999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-295890195709532716705782676426386000000000000)
      constant := (7331317649068171580306863755836479352517092399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48208983737820575153/10000000000000000000)
  centralHi := (482089837378205751531/100000000000000000000)
  directionLo := (484674788012089225253/100000000000000000000)
  directionHi := (242337394006044612627/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree095.table
  base := (23744513946415090659953705127018526666367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-338135495978411678189978003929912954000000000000)
      constant := (8450820335515437186786034225852501127545292890652) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree095.table
  base := (94978055439256209326177507169094644971973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-299037139418911110771994402354386000000000000)
      constant := (7490303876352218337487494153259235171572101773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484674788012089225253/100000000000000000000)
  centralHi := (242337394006044612627/50000000000000000000)
  directionLo := (243623012544885828663/50000000000000000000)
  directionHi := (487246025089771657327/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree096.table
  base := (97838257186957945235076500890312916066697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-341693892491433254400878752087979954000000000000)
      constant := (8632129870176341773136488234354039298414152692033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree096.table
  base := (48919128445190215214343552749798333516361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (342936173457901917471790646000000000000000)
      linear := (-33576009236476611648689569809154000000000000)
      constant := (850110636535446235878570390942567436772456658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243623012544885828663/50000000000000000000)
  centralHi := (487246025089771657327/100000000000000000000)
  directionLo := (122450941145066631487/25000000000000000000)
  directionHi := (489803764580266525949/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree097.table
  base := (5036870274051170923363999012598360793703/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-345252289004454830611779500246046954000000000000)
      constant := (8815363990636233623487582590135164252978941671340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree097.table
  base := (100737405227133045842581325442210858466641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-305331026837667898904417854210386000000000000)
      constant := (7813393206379330190278164772248082442871733241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell094.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122450941145066631487/25000000000000000000)
  centralHi := (489803764580266525949/100000000000000000000)
  directionLo := (49234821684273409727/10000000000000000000)
  directionHi := (492348216842734097271/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree098.table
  base := (103675500637869691262956809531598390821013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3498291905444057460129736379846000000000000000)
      linear := (-348810685517476406822680248404113954000000000000)
      constant := (9000522696806708124503626766670788485397129394157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree098.table
  base := (103675500420545490460509479655997927707677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3086425561121117257246115814000000000000000)
      linear := (-308477970547046292970629580138386000000000000)
      constant := (7977496308957813301756368776780378609967667877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell094.Kernel098
