import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell159.Parameters
import ForestUnimodality.BinomialMassData.Q6_11.Batch000_049
import ForestUnimodality.BinomialMassData.Q6_11.Batch050_099
import ForestUnimodality.BinomialMassData.Q6_11.Batch100_149
import ForestUnimodality.BinomialMassData.Q97_177.Batch000_049
import ForestUnimodality.BinomialMassData.Q97_177.Batch050_099
import ForestUnimodality.BinomialMassData.Q97_177.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel000
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
  base := (662758500072948469683353783/20000000000000000000000000)
  polynomial :=
    { denominator := 55000000000000000000000000000000000000000
      center := (222)
      previous := (0)
      next := (185)
      square := (5346780017612867627607720060000000000000)
      linear := (-22067894781767327661015087900000000000000)
      constant := (1822585875200608291629222903250000000000000) }

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
  base := (662758500072948469683353783/20000000000000000000000000)
  polynomial :=
    { denominator := 885000000000000000000000000000000000000000
      center := (3589)
      previous := (0)
      next := (2960)
      square := (86034551192497960916960586420000000000000)
      linear := (-355092488761165181454515505300000000000000)
      constant := (29327063628227969783488404897750000000000000) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel001
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
  base := (94406773073350467973870899831431172475321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-306908202810795015802458607620000000000000)
      constant := (11573125463350925430313003763563171869513841) }

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
  base := (188147561127313095111900606911963526255213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-53028048961380561023559732135720000000000000)
      constant := (1990836589258220514079040406599795104683189359) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel002
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
  base := (22945453612705221525336128263965589574679/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-742139126044298854667502496680000000000000)
      constant := (14551617332728393602760994561779181692680795) }

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
  base := (28510333347186463010645806801139996650451/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-32077592124471815317743317323020000000000000)
      constant := (624527391494160841690547722075529970041319586) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel003
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
  base := (74714061419913421274038352603737021315219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-870461846467007677730087778120000000000000)
      constant := (10149819594081614881108802247532179579141499) }

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
  base := (74165858724388852532165926110799699688767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-75282319536506700247413537156360000000000000)
      constant := (870842652670669453018218067882121263849793781) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel004
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
  base := (51890109572697896632759148111407691298033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-998784566889716500792673059560000000000000)
      constant := (7897915896938552084565680550600330647061993) }

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
  base := (51481462183858392682304128890030649533333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-86409454824069769859340439666680000000000000)
      constant := (678254872798406803179995883776350073076596519) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel005
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
  base := (18965074421307215944717727989345992792923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-563553643656212661927629170500000000000000)
      constant := (3394274668054063946854656637710865127943683) }

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
  base := (4703288700504723742113823032001954366199/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-48768295055816419735633671088500000000000000)
      constant := (291984404603053108966604863325785637784864628) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel006
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
  base := (28698651873427177027107252057754431026803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-1255430007735134146917843622440000000000000)
      constant := (6321321101485804456487537500108286154243163) }

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
  base := (14232932079486112898711440180430785563639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-54331862699597954541597122343660000000000000)
      constant := (272403746910160763848686164790118693641082077) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel007
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
  base := (22114097297865376268539639255021763302273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-1383752728157842969980428903880000000000000)
      constant := (6244367107631820323854930676337633359575033) }

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
  base := (21928012928051447981212304068209136526583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-119790860686758978695121147197640000000000000)
      constant := (539131851411119867884992041279348012747106269) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel008
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
  base := (17107536194155503594464042811085608087201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-1512075448580551793043014185320000000000000)
      constant := (6428344535011578847479995258221358578551321) }

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
  base := (16952579925932492036470483898935209019771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-130917995974322048307048049707960000000000000)
      constant := (555870464163564660725834038392420387793468553) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel009
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
  base := (409779347133959706569811029797071757659/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-820199084501630308052799733380000000000000)
      constant := (3402381909844883685805251781647130922827824) }

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
  base := (1622467616617463565387705874581841867967/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-71022565630942558959487476109140000000000000)
      constant := (294588543875791549558489082490112698508717524) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel010
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
  base := (9817090456090223338403425417037107102907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-1768720889425969439168184748200000000000000)
      constant := (7335725875981964244975496335461489959451747) }

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
  base := (9700168588835479120738881652504861160521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-153172266549448187530901854728600000000000000)
      constant := (635821416552213734938832762067108265099320803) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel011
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
  base := (879538339482096373125366714810427759399/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55000000000000000000000000000000000000000
      center := (222)
      previous := (0)
      next := (185)
      square := (5346780017612867627607720060000000000000)
      linear := (-86229254993121739192307728620000000000000)
      constant := (363591136261879440977484585011658821413556) }

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
  base := (6932443943283307231721800233684222305441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-164299401837011257142828757238920000000000000)
      constant := (693908892467092534222030401603724333535720363) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel012
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
  base := (4655235177460248045253917112533547348387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-2025366330271387085293355311080000000000000)
      constant := (8780643507102658975119791317496559229154827) }

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
  base := (4562464855055489396393799893351905962263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-175426537124574326754755659749240000000000000)
      constant := (762247946835378589737377180060513953963912509) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel013
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
  base := (1298061764112597717205299930055148125579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-1076844525347047954177970296260000000000000)
      constant := (4835616687086083758283324406376672923195059) }

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
  base := (2513140372950808623867292340324080959059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-186553672412137396366682562259560000000000000)
      constant := (840033518853677592449034012912644377455453137) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel014
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
  base := (401554337293966147661082450471720002587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-1141005885558402365709262936980000000000000)
      constant := (5332007582324333971064992245867078120313027) }

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
  base := (364472625602486626896618394041552782739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-98840403849850232989304732384940000000000000)
      constant := (463342879190236522273987933613255935710143377) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel015
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
  base := (-383020710653833068959011248030642261507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-1205167245769756777240555577700000000000000)
      constant := (5876939400975784577567547775988292286357653) }

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
  base := (-832182851894499543482050714297619942183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-208807942987263535590536367280200000000000000)
      constant := (1021765408381261487844129321502589954943782931) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel016
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
  base := (-428889493786332128572609750111894259827/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-2538657211962222377543696436840000000000000)
      constant := (12936816680234993801498058536702303972804665) }

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
  base := (-220327686356282251521228133883489210381/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-109967539137413302601231634895260000000000000)
      constant := (562463752998567227808961934985753610879956085) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel017
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
  base := (-839682780023545585836262033392147227849/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-1333489966192465600303140859140000000000000)
      constant := (7104803789814958007617592599559100370860542) }

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
  base := (-213181688370088730193587220145112971641/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-115531106781194837407195086150420000000000000)
      constant := (617947289157466958405373517325916681897224296) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel018
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
  base := (-553828507977217959637961300337970057013/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-1397651326403820011834433499860000000000000)
      constant := (7784810740882305895689987749276422492405708) }

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
  base := (-4476771233233747815752703820747758949589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-242189348849952744426317074811160000000000000)
      constant := (1354440033848918592387949127407371153289442073) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel019
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
  base := (-2689028555642718341056531236472562722801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-1461812686615174423365726140580000000000000)
      constant := (8507345105242963496668782459146819910541079) }

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
  base := (-169336057903888079652586598831886144967/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-126658242068757907019121988660740000000000000)
      constant := (740188553263010631518933688344857807809753904) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel020
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
  base := (-3107938536496146155359708113256880294807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-1525974046826528834897018781300000000000000)
      constant := (9271507924861981437937028490295917484328353) }

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
  base := (-781459804521874735581251404051064211803/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-132221809712539441825085439915900000000000000)
      constant := (806775496937968417499959848195978945744565084) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel021
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
  base := (-6956452458255394338600891112436475489073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-3180270814075766492856622844040000000000000)
      constant := (20153102293851352302132396812115186465822167) }

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
  base := (-1746968124654312048714964919260414460999/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-137785377356320976631048891171060000000000000)
      constant := (876916479826461406912670961026606983567574886) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel022
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
  base := (-475630847700585931084215492054980484551/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55000000000000000000000000000000000000000
      center := (222)
      previous := (0)
      next := (185)
      square := (5346780017612867627607720060000000000000)
      linear := (-150390615204476150723600369340000000000000)
      constant := (992895545319809308372281780139161717359512) }

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
  base := (-1527521591841564484066222321379676308581/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-286697890000205022874024684852440000000000000)
      constant := (1901115734207314872853163376335800201547443085) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel023
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
  base := (-8185408316662635042400447011037972895259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-3436916254921184138981793406920000000000000)
      constant := (23613773399891503794339059412544405279673661) }

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
  base := (-1641890763588536710614990774936829093851/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-297825025287768092485951587362760000000000000)
      constant := (2055309831472155170557811234936913468864570035) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel024
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
  base := (-1086198572013747907137512789103850317703/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-1782619487671946481022189344180000000000000)
      constant := (12731223143830788753047405846233736446231748) }

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
  base := (-8710563338296659196601996364700591494613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-308952160575331162097878489873080000000000000)
      constant := (2216340549916976082275824198834791723021756441) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel025
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
  base := (-1825729130669427014585926984109004676541/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-3693561695766601785106963969800000000000000)
      constant := (27388993291618744340147986244614052170692695) }

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
  base := (-4573455168962555206121715051610717535861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-160039647931447115854902696191700000000000000)
      constant := (1192072752482001336221860320071029276773003577) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel026
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
  base := (-4753802684750299846239301081489294995057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-1910942208094655304084774625620000000000000)
      constant := (14696403143703348341492623316099795305598103) }

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
  base := (-9523484830673571923704983752415812367011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-331206431150457301321732294893720000000000000)
      constant := (2558672585898646021941841634439681671451304127) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel027
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
  base := (-245766756038613637162241132230064961817/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-1975103568306009715616067266340000000000000)
      constant := (15736688385235780080873366632043242792402860) }

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
  base := (-9844455621084792905996424437157139720249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-342333566438020370933659197404040000000000000)
      constant := (2739878257895066201135560183642607989901439693) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel028
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
  base := (-1262669332609843973846935102983732631443/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-2039264928517364127147359907060000000000000)
      constant := (16815139749726980738399553720395873406381588) }

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
  base := (-10113305734398720111855407139897731418819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-353460701725583440545586099914360000000000000)
      constant := (2927726147720682446086036956769087990793273183) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel029
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
  base := (-5161298860427825649265617740266110256567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-2103426288728718538678652547780000000000000)
      constant := (17931579422029128136132879414987800658955393) }

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
  base := (-10332945368515038263651742251569888323293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-364587837013146510157513002424680000000000000)
      constant := (3122185864178828349237564023906615656239851201) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel030
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
  base := (-1312107183461261567557891642872814893079/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-2167587648940072950209945188500000000000000)
      constant := (19085858690346223937965617170849557591749764) }

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
  base := (-2101161234315137982926804354812353272453/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-375714972300709579769439904935000000000000000)
      constant := (3323232013567957604506566338779472973878866605) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel031
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
  base := (-10626189672248100028057805435592975046133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-4463498018302854723482475658440000000000000)
      constant := (40555706361081747321905651549413250019417907) }

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
  base := (-5316959984210779068166494163547381111323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-193421053794136324690683403722660000000000000)
      constant := (1765421688770628434988524178104954699054453911) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel032
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
  base := (-2678078421030831680051288197101591193411/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-2295910369362781773272530469940000000000000)
      constant := (21507458871962661301081666250541414931194538) }

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
  base := (-10718984518689211302483544143821432664663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-397969242875835718993293709955640000000000000)
      constant := (3745002226394841462122096492177112778682924291) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel033
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
  base := (-10756667495859027755000713207873008340279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (444)
      previous := (0)
      next := (370)
      square := (10693560035225735255215440120000000000000)
      linear := (-429103950831661124509786020120000000000000)
      constant := (4140834321102312713181337917993396908256931) }

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
  base := (-5381209225717840291723608770519774601461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-204548189081699394302610306232980000000000000)
      constant := (1982846872692734402214812653234381993836942777) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel034
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
  base := (-2152090757973521656678375709218552685287/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-4848466179570981192670231502760000000000000)
      constant := (48158340201110198027135170925842775625401365) }

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
  base := (-10765407162036176606747289775449249576973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-420223513450961858217147514976280000000000000)
      constant := (4192905555429235572316409172921143486667670961) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel035
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
  base := (-536233922351759919704718278741466488039/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-2488394449996845007866408392100000000000000)
      constant := (25421142019646187703925046127722825549472810) }

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
  base := (-2682235290078190190050500291054972259667/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-215675324369262463914537208743300000000000000)
      constant := (2213313656316034989354731103951025849384595038) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel036
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
  base := (-10650182752248553375027769697317709243661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-5105111620416398838795402065640000000000000)
      constant := (53600907251200674597301210042944557181517019) }

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
  base := (-10653848112484903143755198554491861773673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-442477784026087997441001319996920000000000000)
      constant := (4666850373675642097355070818786801487497532861) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel037
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
  base := (-10537670329095025801411052386893145030921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-5233434340839107661857987347080000000000000)
      constant := (56434124698381025933887029950065929451258559) }

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
  base := (-5270409807234648279620623814886164196579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-226802459656825533526464111253620000000000000)
      constant := (2456783758111896952661839362371263787295125503) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel038
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
  base := (-10387729666649142107020821450242545475353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-5361757061261816484920572628520000000000000)
      constant := (59341865173655411719120582432200651997482287) }

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
  base := (-10390433563099483780745503845072813952831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-464732054601214136664855125017560000000000000)
      constant := (5166772705299892715425512558752544603890585867) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel039
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
  base := (-81606823678768001008093730135027843461/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-5490079781684525307983157909960000000000000)
      constant := (62324069121436685115069156124427703867652375) }

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
  base := (-10203172849178764817865470999541096508239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-475859189888777206276782027527880000000000000)
      constant := (5426460898075279665660345588642352329164460123) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel040
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
  base := (-9977451866774621641876615799314564275021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-5618402502107234131045743191400000000000000)
      constant := (65380686731096074485930112672282937722722459) }

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
  base := (-9979440977171631915395772406803629379319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-486986325176340275888708930038200000000000000)
      constant := (5692627880752832063515787563147749698391771683) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel041
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
  base := (-4858935343723040177123265755019466651863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-2873362611264971477054164236420000000000000)
      constant := (34255838171166119957024049844402644535124577) }

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
  base := (-2429893779214932770764243578890564469551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-249056730231951672750317916274260000000000000)
      constant := (2982635066134260089856163304466771670488957814) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel042
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
  base := (-4711198693001249906727963241190971285061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-2937523971476325888585456877140000000000000)
      constant := (35858501555741992224916323570455892474507619) }

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
  base := (-1884771401837431914171575866512802123633/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-509240595751466415112562735058840000000000000)
      constant := (6244384710401664806668120800377474037114502905) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel043
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
  base := (-9091272809271579713891353526585117367157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-6003370663375360600233499035720000000000000)
      constant := (74996637896085156430262982138563200798574003) }

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
  base := (-1136565259886551678983338822405541936267/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-260183865519514742362244818784580000000000000)
      constant := (3264984578304816615050489341711195702238254876) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel044
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
  base := (-4362349198408565989168140141363338857563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55000000000000000000000000000000000000000
      center := (222)
      previous := (0)
      next := (185)
      square := (5346780017612867627607720060000000000000)
      linear := (-278713335627184973786185650780000000000000)
      constant := (3561388923724933391485559322605003272566807) }

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
  base := (-545360440632293295100739115519328968911/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-265747433163296277168208270039740000000000000)
      constant := (3411010708254242348915508808819533180621299416) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel045
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
  base := (-416142131466785621107670246264807212779/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-3130008052110389123179334799300000000000000)
      constant := (40889369001454917871715864769019583272537410) }

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
  base := (-8323756307110216500876232539609735311557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-542622001614155623948343442589800000000000000)
      constant := (7120539773427228372206480656750855534141410249) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel046
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
  base := (-985730802731782295898499182585295359703/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-3194169412321743534710627440020000000000000)
      constant := (42640582944125400203283989136988717045903748) }

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
  base := (-7886627212859939680174176930589645203681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-553749136901718693560270345100120000000000000)
      constant := (7425522792886280083096867526882412335137959317) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel047
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
  base := (-7413827634399328678284866003307909184073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-6516661545066195892483840161480000000000000)
      constant := (88857825716908214979444828071279742988727167) }

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
  base := (-1482898910124526150986569898771839924967/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-564876272189281763172197247610440000000000000)
      constant := (7736969276204089397104432077928268378317848095) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel048
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
  base := (-1726721211138232954400188363674329315633/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-3322492132744452357773212721460000000000000)
      constant := (46254352780497328219070657245430812305616814) }

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
  base := (-863431779533947028214093735373236916033/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-288001703738422416392062075060380000000000000)
      constant := (4027439110865595791651910506003109147543469524) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel049
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
  base := (-1591275125669534244134572576004973141499/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-3386653492955806769304505362180000000000000)
      constant := (48116897722008096705248859379766796499757242) }

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
  base := (-1273117284027669472558011473830442436793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-587130542764407902396051052631080000000000000)
      constant := (8379248792457674042919540188987303448162853505) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel050
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
  base := (-1447135892708244556511014983129032078109/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-3450814853167161180835798002900000000000000)
      constant := (50016543510781901886964752144082774237097622) }

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
  base := (-5788958078888716797447641868458664981119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-598257678051970972007977955141400000000000000)
      constant := (8710080288946216112363102598337686161602174283) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel051
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
  base := (-5177271729860740043605450489013950552301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-7029952426757031184734181287240000000000000)
      constant := (103906573314255450106660697110749311983171579) }

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
  base := (-5177625181275275033714655602967514649857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-609384813339534041619904857651720000000000000)
      constant := (9047372126715134489000931803402370244511543349) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel052
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
  base := (-1132833306329822841864733049603706402079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-3579137573589870003898383284340000000000000)
      constant := (53927124242189315133582342165035903050696882) }

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
  base := (-4531634497824920551206554993641381363743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-620511948627097111231831760162040000000000000)
      constant := (9391123817339816772010403592777243054418431851) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel053
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
  base := (-3850768411349068925117014689463290281553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-7286597867602448830859351850120000000000000)
      constant := (111876107649082351411412452281054941875932087) }

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
  base := (-1925512556500638368564856879682721033629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-315819541957330090421879331336180000000000000)
      constant := (4870667476330604671179460902857993344245812353) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel054
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
  base := (-3135611041908391422631393000284397400071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-7414920588025157653921937131560000000000000)
      constant := (115972146724137656975971745864085587914591409) }

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
  base := (-1567914844378816747702781765625529920091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-321383109601111625227842782591340000000000000)
      constant := (5049002595795266996789917465847452591044489687) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel055
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
  base := (-1192944675358194210501850947141322660613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55000000000000000000000000000000000000000
      center := (222)
      previous := (0)
      next := (185)
      square := (5346780017612867627607720060000000000000)
      linear := (-342874695838539385317478291500000000000000)
      constant := (5461016467875660558361880330581445450733257) }

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
  base := (-74564860011059012961276345725358739499/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-326946677244893160033806233846500000000000000)
      constant := (5230567124541695807577034818953441258934591088) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel056
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
  base := (-1601626954478992546943181371718361577569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-7671566028870575300047107694440000000000000)
      constant := (124386751498841559487549498467142078249114151) }

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
  base := (-1601785418591025153344155050996224011579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-665020489777349389679539370203320000000000000)
      constant := (10830721886926587534739580066400206432647080503) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel057
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
  base := (-782843608315587712608664572582896702367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-7799888749293284123109692975880000000000000)
      constant := (128705311950499293133364920637197469499013593) }

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
  base := (-782978447001538656289424672331383564271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-676147625064912459291466272713640000000000000)
      constant := (11206767906039651907624332636543883361438317947) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel058
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
  base := (70444162428113104291244609482559466503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-7928211469715992946172278257320000000000000)
      constant := (133098041648670901951104892711827389695446863) }

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
  base := (17582365539435094156473535340097274617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-343637380176237764451696587611980000000000000)
      constant := (5794636070021013325405275698466033271677650662) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel059
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
  base := (479111266876535062888542306329984498197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-4028267095069350884617431769380000000000000)
      constant := (68782469460326251063816949921025928124281837) }

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
  base := (958124993184531516514278050456426431217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1770000000000000000000000000000000000000000
      center := (7178)
      previous := (0)
      next := (5920)
      square := (172069102384995921833921172840000000000000)
      linear := (-11837320265085399974835933520920000000000000)
      constant := (203020922879285302538633287141170787478325409) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel060
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
  base := (235059992630995717915411184637719525591/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-4092428455280705296148724410100000000000000)
      constant := (71053001183563062116160174273364656250386044) }

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
  base := (1880397016831800872537631891677631154241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-709529030927601668127246980244600000000000000)
      constant := (12373654719324343729608748041944789502143738763) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel061
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
  base := (2837206709448873354453846208093031863443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-8313179630984119415360034101640000000000000)
      constant := (146721230817433233146264641253499256855476603) }

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
  base := (1418568115458878791937704044316044754419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-360328083107582368869586941377460000000000000)
      constant := (6387766425619437424169577360219472455370397617) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel062
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
  base := (478549343085438662863164906456166783913/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-4220751175703414119211309691540000000000000)
      constant := (75705311646083441273529451130164784723413892) }

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
  base := (3828334860019980818083993013015864663993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-731783301502727807351100785265240000000000000)
      constant := (13183868764422689865217375319691164674686078899) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel063
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
  base := (4854037274502535167878711881495360225763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-8569825071829537061485204664520000000000000)
      constant := (156174178971884902485786452963340938587317323) }

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
  base := (4853986404539789572490863394535227854381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-742910436790290876963027687775560000000000000)
      constant := (13598662391000479754532500679189771384483300783) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel064
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
  base := (5914128632419995527880991156316841617537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-8698147792252245884547789945960000000000000)
      constant := (161011897170942492356446636376634337835721977) }

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
  base := (2957042715510009114700141052346929321711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-377018786038926973287477295142940000000000000)
      constant := (7009956837115325667869467108050938982906627973) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel065
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
  base := (1401732815367912511000759777702340215959/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-8826470512674954707610375227400000000000000)
      constant := (165923777315606496491862541159509915830655195) }

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
  base := (7008627396933842254982082188590176822607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-765164707365417016186881492796200000000000000)
      constant := (14447622566675596980229887496917447216558484901) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel066
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
  base := (4068819819888091278564305749263184298027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55000000000000000000000000000000000000000
      center := (222)
      previous := (0)
      next := (185)
      square := (5346780017612867627607720060000000000000)
      linear := (-407036056049893796848770932220000000000000)
      constant := (7768628132988669245240355725401895027278297) }

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
  base := (4068804252138689588080459282909606869311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-388145921326490042899404197653260000000000000)
      constant := (7440894514336381071669517346480905024536214773) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel067
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
  base := (9301052000330253260200109083866286717623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-9083115953520372353735545790280000000000000)
      constant := (175970021599546321191561797066427820692832383) }

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
  base := (9301025577230541319507591117540371902923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-787418977940543155410735297816840000000000000)
      constant := (15322413027057057649492754667393914103782224889) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel068
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
  base := (1312362297357992635605783401407882611889/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-4605719336971540588399065535860000000000000)
      constant := (90552192500328556008790219762921415184154276) }

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
  base := (10498875959929179658922252216355597832733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-798546113228106225022662200327160000000000000)
      constant := (15769494534093294190411486711440841508167230719) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel069
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
  base := (2932794112123011888087835128974426340951/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-4669880697182894999930358176580000000000000)
      constant := (93156454423764993428709574073971811174510142) }

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
  base := (11731157431042118006163671699618125267071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-809673248515669294634589102837480000000000000)
      constant := (16223033526584110293161427658514072082164022453) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel070
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
  base := (12997884261054173972844686031950094393641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-9468084114788498822923301634600000000000000)
      constant := (191595592904437537469603575133865961421630561) }

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
  base := (259957362647805570112068944655149464987/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-410400191901616182123258002673900000000000000)
      constant := (8341514992562270923848125051516843146571481025) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel071
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
  base := (7149510092599280967130679366732829553417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-4798203417605603822992943458020000000000000)
      constant := (98476218486993100543136931067734672375963457) }

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
  base := (14299006509299327840977109164624627362803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-831927519090795433858442907858120000000000000)
      constant := (17149483893479124791194204188432734983549751729) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel072
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
  base := (15634582854595747756896006417871060321543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-9724729555633916469048472197480000000000000)
      constant := (202383440890850112602185661536242398298906703) }

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
  base := (15634571260756822508044944818375349934461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-843054654378358503470369810368440000000000000)
      constant := (17622395238061386176140514595226933779365576223) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel073
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
  base := (17004571124624476907146625521521721877213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-9853052276056625292111057478920000000000000)
      constant := (207888604516530100218773130904984128347142773) }

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
  base := (17004561297761978953094086569674493130387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-854181789665921573082296712878760000000000000)
      constant := (18101764007498890819883757846815350731760631441) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel074
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
  base := (18408984036143562726025152198746280151419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-9981374996479334115173642760360000000000000)
      constant := (213467927734970080350298714516368299898321699) }

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
  base := (18408975708521199715124606418634771331897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-865308924953484642694223615389080000000000000)
      constant := (18587590192269778184138711695095162917019000371) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel075
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
  base := (19847820785190226960213964258318761218077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-10109697716902042938236228041800000000000000)
      constant := (219121410448890556828110980085256570107387317) }

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
  base := (496195343234098064949548224066349496949/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-438218030120523856153075258949700000000000000)
      constant := (9539936892199518293945466954568497755932768140) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel076
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
  base := (10660540348817595323935854764048144849891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-5119010218662375880649406661620000000000000)
      constant := (112424526288360943448913561999409825526836811) }

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
  base := (533026868010959739377294454523647466879/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-443781597764305390959038710204860000000000000)
      constant := (9789307388602347061034454662227889009932347940) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel077
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
  base := (22828763207983467536386585523776662162219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (444)
      previous := (0)
      next := (370)
      square := (10693560035225735255215440120000000000000)
      linear := (-942394832522496416760127145880000000000000)
      constant := (20968259459094470656625556196041543283784409) }

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
  base := (1141437907270077056515810972097334006277/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-449345165408086925765002161460020000000000000)
      constant := (10041906582542860108072804744847044590275507110) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel078
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
  base := (24370867841642528978595795364513450851339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-10494665878170169407423983886120000000000000)
      constant := (236526814811416731836966264135586127553012019) }

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
  base := (6092715888611607880759521547133953031703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-454908733051868460570965612715180000000000000)
      constant := (10297734471672390467875884667247959743020148858) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel079
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
  base := (25947394200090508370266214716551792330589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-10622988598592878230486569167560000000000000)
      constant := (242476934812633404880970353891822766872001269) }

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
  base := (12973695285059255103246799047392062593859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-460472300695649995376929063970340000000000000)
      constant := (10556791054020059204763767350458795309667669537) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel080
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
  base := (27558341948469948522030883086766132485037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-10751311319015587053549154449000000000000000)
      constant := (248501214013171444034979985205498702030689477) }

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
  base := (27558338875462316402513273281024672018637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-932071736678863060365785030451000000000000000)
      constant := (21638152655861766760566481689689740649890626191) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel081
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
  base := (29203710805210239218748492545208910472339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-10879634039438295876611739730440000000000000)
      constant := (254599652378960805462963059817090278167153019) }

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
  base := (9345186625316961788469602470059531573/3200000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-943198871966426129977711932961320000000000000)
      constant := (22169180584028104025024010845944609025677621875) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel082
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
  base := (30883500533346830536007458233636263399653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-11007956759861004699674325011880000000000000)
      constant := (260772249881328778624065775958749987871358013) }

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
  base := (30883498332030106595257159279805405578267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-954326007253989199589638835471640000000000000)
      constant := (22706665890199397239965555328432047850453842281) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel083
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
  base := (8149427733314904847252282147765586253751/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-5568139740141856761368455146660000000000000)
      constant := (133509503248060665522513748395799271873407742) }

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
  base := (3259770907055353346761515598510426990789/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-482726571270776134600782868990980000000000000)
      constant := (11625304286202773725137962802240141945324047635) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel084
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
  base := (17173170918299165593442174154184615436201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-5632301100353211172899747787380000000000000)
      constant := (136669961101484039750176527261616338467780321) }

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
  base := (34346340260645849641833662231534125278017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-976580277829115338813492640492280000000000000)
      constant := (23801008628985700598415099246884070870278331531) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel085
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
  base := (451617413765008871319062765338465164943/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-5696462460564565584431040428100000000000000)
      constant := (139867498492333695493462684759238171398324120) }

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
  base := (2258086985502907858711352939387416950547/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-493853706558339204212709771501300000000000000)
      constant := (12178933029268886988041538349513182361716498568) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel086
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
  base := (18973432303420551367309609091151298049669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-5760623820775919995962333068820000000000000)
      constant := (143102115413335980793648349174189307064009949) }

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
  base := (2371678967452164694017612300153645171683/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-499417274202120739018673222756460000000000000)
      constant := (12460590429938134273105743437602716132223084552) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel087
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
  base := (39798756251673606015040942778693167465739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-11649570361974548814987251419080000000000000)
      constant := (292747623716658436886112795449101873263354419) }

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
  base := (9949688824513021555379978645987315414277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-504980841845902273824636674011620000000000000)
      constant := (12745476515998502679554518258261211069742589422) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel088
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
  base := (4168506794925615430286111886332676249121/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55000000000000000000000000000000000000000
      center := (222)
      previous := (0)
      next := (185)
      square := (5346780017612867627607720060000000000000)
      linear := (-535358776472602619911356213660000000000000)
      constant := (13607507983825787590402647391188297193701655) }

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
  base := (5210633392860116038717842682432836230073/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-510544409489683808630600125266780000000000000)
      constant := (13033591287023824077383026770062904435002609356) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel089
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
  base := (2180289981303026884299563754633226433197/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-5953107901409983230556210990980000000000000)
      constant := (153028443300150859248085167393466203984168370) }

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
  base := (4360579894428367912268872684147762997221/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-516107977133465343436563576521940000000000000)
      constant := (13324934742651530653042414286615055444899894515) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel090
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
  base := (45560951219388868700845453777151455090731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-12034538523242675284175007263400000000000000)
      constant := (312822756577475167024955171111035326065978451) }

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
  base := (9112190128606118354775924692667046295961/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-1043343089554493756485054055554200000000000000)
      constant := (27239013765144708566329869279629609822343603615) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel091
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
  base := (5943815334453753639870420324048571168687/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-6081430621832692053618796272420000000000000)
      constant := (159831392784600363634784528103599508445644508) }

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
  base := (47550522188450284398656554118125090466989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-1054470224842056826096980958064520000000000000)
      constant := (27834615413043428694688543004652540319746766127) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel092
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
  base := (49574513948800500811688250446621207536761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-12291183964088092930300177826280000000000000)
      constant := (326576973569914393536444523193321166111948081) }

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
  base := (24787256768525303631568088332728541742591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-532798680064809947854453930287420000000000000)
      constant := (14218337214272516585744953003163404161417877813) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel093
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
  base := (12908231249830770260829710126978040829541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-6209753342255400876681381553860000000000000)
      constant := (166782660287413662147280858786368685880748922) }

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
  base := (12908231162841338645193539398444959432951/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-538362247708591482660417381542580000000000000)
      constant := (14522595405629131204852537904895641422716614586) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel094
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
  base := (53725755793004590100544174357551172926483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-12547829404933510576425348389160000000000000)
      constant := (340627826579802144798610013376783691924104443) }

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
  base := (2149030219959589011317547754121027309697/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-1087851630704746034932761665595480000000000000)
      constant := (29660164560844713071774330495794107204879144275) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel095
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
  base := (27926503150090020947730942984411477793501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-6338076062678109699743966835300000000000000)
      constant := (173882245790624695865976612158113788813013621) }

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
  base := (13963251512943383586642073759657718939031/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-549489382996154552272344284052900000000000000)
      constant := (15140797838505206387750919460020211117760601466) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel096
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
  base := (5801467649499606978235712328621213492369/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-6402237422889464111275259476020000000000000)
      constant := (177487657788020403865229926646175834162883245) }

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
  base := (11602935257029254247802304847962681992299/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-1110105901279872174156615470616120000000000000)
      constant := (30909484159498771679395122126870931440227892285) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel097
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
  base := (60210766354810850672229088718559410440813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-12932797566201637045613104233480000000000000)
      constant := (362260298561436732200360803796625688663338373) }

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
  base := (15052691544388089850064925329427446154613/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-560616518283717621884271186563220000000000000)
      constant := (15771915004042342448719004734797741640385247118) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel098
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
  base := (62441275859691493102357204474024662441617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-13061120286624345868675689514920000000000000)
      constant := (369619440535025285274666885916236984155435657) }

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
  base := (62441275709978528153367755529061684598831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-1132360171854998313380469275636760000000000000)
      constant := (32184633222569596843951163574442231172265592133) }

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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (490166313711818306331/100000000000000000000)
  centralHi := (122541578427954576583/25000000000000000000)
  directionLo := (19707458624502971077/4000000000000000000)
  directionHi := (246343232806287138463/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree099.table
  base := (64706204991992968392712779839691775975633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (444)
      previous := (0)
      next := (370)
      square := (10693560035225735255215440120000000000000)
      linear := (-1199040273367914062885297708760000000000000)
      constant := (34277521954061038043917693461356609535731963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree099.table
  base := (32353102432779090540860229903895861982283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-571743653571280691496198089073540000000000000)
      constant := (16415946901388684826277935812580064486680981369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19707458624502971077/4000000000000000000)
  centralHi := (246343232806287138463/50000000000000000000)
  directionLo := (495193792063054837279/100000000000000000000)
  directionHi := (3094961200394092733/625000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree100.table
  base := (13401110747201053613439031804553887214411/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-13317765727469763514800860077800000000000000)
      constant := (384560201438474220800035850921755101764718655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree100.table
  base := (67005553629240128885540132823748473824313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-1154614442430124452604323080657400000000000000)
      constant := (33485611748550823753394555295618405312147300659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (495193792063054837279/100000000000000000000)
  centralHi := (3094961200394092733/625000000000000000)
  directionLo := (248844243452488593247/50000000000000000000)
  directionHi := (99537697380995437299/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree101.table
  base := (8667415259707206086987238560255132917071/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-6723044223946236168931722679620000000000000)
      constant := (196070910182365566135235937999123484331862364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree101.table
  base := (8667415248438891296301531269249154061519/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-582870788858843761108124991583860000000000000)
      constant := (17072893529874420184336971853634155663457771668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248844243452488593247/50000000000000000000)
  centralHi := (99537697380995437299/20000000000000000000)
  directionLo := (500170739145887366577/100000000000000000000)
  directionHi := (250085369572943683289/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree102.table
  base := (71707510004270646944210784152425141776443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-13574411168315181160926030640680000000000000)
      constant := (399797598271907937830914863772523442154949603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree102.table
  base := (17926877482040854914884346974568564014317/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-588434356502625295914088442839020000000000000)
      constant := (17406209868121966899671310238159759028003024862) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (500170739145887366577/100000000000000000000)
  centralHi := (250085369572943683289/50000000000000000000)
  directionLo := (125660183281569186513/25000000000000000000)
  directionHi := (502640733126276746053/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree103.table
  base := (74110117504348071206029718575342189511421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-13702733888737889983988615922120000000000000)
      constant := (407527535158613598297026222082096404930881941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree103.table
  base := (37055058720049923526827010994825617607683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-593997924146406830720051894094180000000000000)
      constant := (17742754888960108255545598753470483924677033569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125660183281569186513/25000000000000000000)
  centralHi := (502640733126276746053/100000000000000000000)
  directionLo := (252549324339671624617/50000000000000000000)
  directionHi := (101019729735868649847/20000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree104.table
  base := (9568393070925306315036318921669572327617/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-6915528304580299403525600601780000000000000)
      constant := (207665815511789564841258593760648073006566628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree104.table
  base := (38273572256585236030171159538679472324043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-599561491790188365526015345349340000000000000)
      constant := (18082528592335846337678667239725309729479981049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252549324339671624617/50000000000000000000)
  centralHi := (101019729735868649847/20000000000000000000)
  directionLo := (253772330641894583587/50000000000000000000)
  directionHi := (20301786451351566687/4000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree105.table
  base := (39509295591904243655316374222111701470279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-6979689664791653815056893242500000000000000)
      constant := (211604942932819935490324067731875515877903759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree105.table
  base := (79018591138035459143701614513588564330707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-1210250118867939800663957593209000000000000000)
      constant := (36851061956400826389639620752931405377305573201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253772330641894583587/50000000000000000000)
  centralHi := (20301786451351566687/4000000000000000000)
  directionLo := (509978942210022953083/100000000000000000000)
  directionHi := (127494735552505738271/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree106.table
  base := (81524457344679951960894844610052178664349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-14087702050006016453176371766440000000000000)
      constant := (431162299683720588407863528622936313618386229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree106.table
  base := (81524457306049972432939754952179031920589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-1221377254155502870275884495719320000000000000)
      constant := (37543524093017339632939373869989365630346710927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509978942210022953083/100000000000000000000)
  centralHi := (127494735552505738271/25000000000000000000)
  directionLo := (256200829330054856551/50000000000000000000)
  directionHi := (512401658660109713103/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree107.table
  base := (84064743041766202875710357973411793181267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-14216024770428725276238957047880000000000000)
      constant := (439188872476822954331124022689262826974933307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree107.table
  base := (10508092876145934040051086217751268391947/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-616252194721532969943905699114820000000000000)
      constant := (19121221797218601196066962618837425983268410084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256200829330054856551/50000000000000000000)
  centralHi := (512401658660109713103/100000000000000000000)
  directionLo := (514812973901794013277/100000000000000000000)
  directionHi := (257406486950897006639/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree108.table
  base := (86639448267365139338276486703892707533739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-14344347490851434099301542329320000000000000)
      constant := (447289604244015014563696478641251017611582419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree108.table
  base := (86639448239858407426321895436297773820391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-1243631524730629009499738300739960000000000000)
      constant := (38947820460581783562164164191633097652006343213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514812973901794013277/100000000000000000000)
  centralHi := (257406486950897006639/50000000000000000000)
  directionLo := (25860652369844950429/5000000000000000000)
  directionHi := (517213047396899008581/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree109.table
  base := (713988584113999328993432313062309066563/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-14472670211274142922364127610760000000000000)
      constant := (455464494984422320833426779286987424631765375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree109.table
  base := (1784971459820835778046005980146287341793/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-627379330009096039555832601625140000000000000)
      constant := (19829827345688568188243234036117771967758607475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25860652369844950429/5000000000000000000)
  centralHi := (517213047396899008581/100000000000000000000)
  directionLo := (64950254365548455487/12500000000000000000)
  directionHi := (519602034924387643897/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree110.table
  base := (91892117275607185152929761314165492915843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (444)
      previous := (0)
      next := (370)
      square := (10693560035225735255215440120000000000000)
      linear := (-1327362993790622885947882990200000000000000)
      constant := (42155776790656405274779622354455820422074273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree110.table
  base := (2297302931400688661085397480665315967371/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-632942897652877574361796052880300000000000000)
      constant := (20188973143376698215453236881326757892945107060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64950254365548455487/12500000000000000000)
  centralHi := (519602034924387643897/100000000000000000000)
  directionLo := (652475110872943343/125000000000000000)
  directionHi := (521980088698354674401/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree111.table
  base := (94570081044984994418171945448439546300537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-14729315652119560568489298173640000000000000)
      constant := (472036753381628739938374516833581185102364977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree111.table
  base := (94570081028467910009946721442440299038987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-1277012930593318218335519008270920000000000000)
      constant := (41102695246644273962899364681598764042864141241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (652475110872943343/125000000000000000)
  centralHi := (521980088698354674401/100000000000000000000)
  directionLo := (262173678740601203477/50000000000000000000)
  directionHi := (104869471496240481391/20000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree112.table
  base := (97282464316248779709466589303965593341369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-14857638372542269391551883455080000000000000)
      constant := (480434121036904884311359672820659836794305649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree112.table
  base := (24320616075579087316319619868179641926367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-644070032940440643973722955390620000000000000)
      constant := (20916950785493312528079938919235920001274101162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262173678740601203477/50000000000000000000)
  centralHi := (104869471496240481391/20000000000000000000)
  directionLo := (263351993346119143369/50000000000000000000)
  directionHi := (526703986692238286739/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree113.table
  base := (4001170683341765599548581201853369465489/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-14985961092964978214614468736520000000000000)
      constant := (488905647662340508615921315157286442633104225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree113.table
  base := (100029267071792843423546755966634493124971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-1299267201168444357559372813291560000000000000)
      constant := (42571565259720088953621231122878204011704072153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263351993346119143369/50000000000000000000)
  centralHi := (526703986692238286739/100000000000000000000)
  directionLo := (132262529627979665831/25000000000000000000)
  directionHi := (21162004740476746533/4000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree114.table
  base := (102810489341265300880169919034551137742641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-15114283813387687037677054017960000000000000)
      constant := (497451333257257314152594196157900687666859561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree114.table
  base := (12851311166419306918457759032088192468173/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-655197168228003713585649857900940000000000000)
      constant := (21657843156393390381380399554546667975780522556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132262529627979665831/25000000000000000000)
  centralHi := (21162004740476746533/4000000000000000000)
  directionLo := (3321161824887188711/625000000000000000)
  directionHi := (531385891981950193761/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree115.table
  base := (105626131084028349405765512933171352132563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-15242606533810395860739639299400000000000000)
      constant := (506071177821003847451032179378913733608040123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree115.table
  base := (52813065537835175922276617077485796305051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-660760735871785248391613309156100000000000000)
      constant := (22033132365065515296271669658106184170813647593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3321161824887188711/625000000000000000)
  centralHi := (531385891981950193761/100000000000000000000)
  directionLo := (8339241298460129827/1562500000000000000)
  directionHi := (533711443101448308929/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree116.table
  base := (21695238461329694512086784529498846567259/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-15370929254233104683802224580840000000000000)
      constant := (514765181352952746137622110739866802173191695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree116.table
  base := (108476192299600552600576935409181582219089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-1332648607031133566395153520822520000000000000)
      constant := (44823300511699161628553474697043043263113946427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8339241298460129827/1562500000000000000)
  centralHi := (533711443101448308929/100000000000000000000)
  directionLo := (67003363114917615141/12500000000000000000)
  directionHi := (536026904919340921129/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree117.table
  base := (111360673004120557353748106048909632330421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-15499251974655813506864809862280000000000000)
      constant := (523533343852498391540522318143198065511980941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree117.table
  base := (1113606729981778076240449077597682231261/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-671887871159348318003540211666420000000000000)
      constant := (22793396828719650439564002333075349777052931150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67003363114917615141/12500000000000000000)
  centralHi := (536026904919340921129/100000000000000000000)
  directionLo := (4205721934556211159/781250000000000000)
  directionHi := (538332407623195028353/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree118.table
  base := (114279573171602614541118126041782086852449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-15627574695078522329927395143720000000000000)
      constant := (532375665319054902961137419200335632509146329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree118.table
  base := (2856989329164802530141658646740304964973/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 885000000000000000000000000000000000000000
      center := (3589)
      previous := (0)
      next := (2960)
      square := (86034551192497960916960586420000000000000)
      linear := (-11482227776324234793381418015620000000000000)
      constant := (392853764129671333476396655452540679576004420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4205721934556211159/781250000000000000)
  centralHi := (538332407623195028353/100000000000000000000)
  directionLo := (135157019656158505323/25000000000000000000)
  directionHi := (540628078624634021293/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree119.table
  base := (58616446402200787886311370829331164962383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-7877948707750615576494990212580000000000000)
      constant := (270646072876027209564563471877109070960448343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree119.table
  base := (58616446400088681219982754458916243337853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-683015006446911387615467114176740000000000000)
      constant := (23566576020618091631673996783698942329177198879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135157019656158505323/25000000000000000000)
  centralHi := (540628078624634021293/100000000000000000000)
  directionLo := (135728510660376068619/25000000000000000000)
  directionHi := (542914042641504274477/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree120.table
  base := (24044126379592217419211512677106105631013/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-15884220135923939976052565706600000000000000)
      constant := (550282785150945621216274160673649193906762865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree120.table
  base := (120220631894400030919110176895260746281361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-1377157148181385844842861130863800000000000000)
      constant := (47916017279196854647188577464589207973416252923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135728510660376068619/25000000000000000000)
  centralHi := (542914042641504274477/100000000000000000000)
  directionLo := (54519042177694095851/10000000000000000000)
  directionHi := (545190421776940958511/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree121.table
  base := (7702674402990686437577773842887699089617/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55000000000000000000000000000000000000000
      center := (222)
      previous := (0)
      next := (185)
      square := (5346780017612867627607720060000000000000)
      linear := (-727842857106665854505234135820000000000000)
      constant := (25424890159781475417993068480934117519886296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree121.table
  base := (24648558088969836705504471182090881577063/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-1388284283468948914454788033374120000000000000)
      constant := (48705339881137168231640576044765435381546344545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54519042177694095851/10000000000000000000)
  centralHi := (545190421776940958511/100000000000000000000)
  directionLo := (547457335595474905143/100000000000000000000)
  directionHi := (68432166949434363143/12500000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree122.table
  base := (126299368449758176440784171809921991487917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-16140865576769357622177736269480000000000000)
      constant := (568486540844273049535111699552680560970037957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree122.table
  base := (126299368447227976179891239089246743009457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-1399411418756511984066714935884440000000000000)
      constant := (49501119847012252073921088551739643737247759451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547457335595474905143/100000000000000000000)
  centralHi := (68432166949434363143/12500000000000000000)
  directionLo := (109942980239262950607/20000000000000000000)
  directionHi := (137428725299078688259/25000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree123.table
  base := (2587807317989574862879851691960740937079/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-8134594148596033222620160775460000000000000)
      constant := (288849828568839358698656966634621241334663975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree123.table
  base := (129390365897346194401629627163417483549173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-1410538554044075053678641838394760000000000000)
      constant := (50303357176778347764272000863553808780704013639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109942980239262950607/20000000000000000000)
  centralHi := (137428725299078688259/25000000000000000000)
  directionLo := (27598161664196573239/5000000000000000000)
  directionHi := (551963233283931464781/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree124.table
  base := (13251578279291101442385102813421278398903/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-8198755508807387634151453416180000000000000)
      constant := (293493466197456580435662479066279873431336315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree124.table
  base := (132515782791113740140326457182723997478913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-1421665689331638123290568740905080000000000000)
      constant := (51112051870392742408731984249818546705672288459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27598161664196573239/5000000000000000000)
  centralHi := (551963233283931464781/100000000000000000000)
  directionLo := (27710122211803280139/5000000000000000000)
  directionHi := (554202444236065602781/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree125.table
  base := (135675619126049522705733895203345272998537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-16525833738037484091365492113800000000000000)
      constant := (596348366615491718380615075669604778032822977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree125.table
  base := (135675619124534910198081554732752926140107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-1432792824619201192902495643415400000000000000)
      constant := (51927203927813708878805367189124138807681137401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27710122211803280139/5000000000000000000)
  centralHi := (554202444236065602781/100000000000000000000)
  directionLo := (278216322084635726603/50000000000000000000)
  directionHi := (556432644169271453207/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree126.table
  base := (138869874894979669138520750816409582243903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-16654156458460192914428077395240000000000000)
      constant := (605783959798940723464198713246705559451512263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree126.table
  base := (17358734361712918136148269845140084227459/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-721959979953382131257211272962860000000000000)
      constant := (26374406674500226531191446544900271598349417348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278216322084635726603/50000000000000000000)
  centralHi := (556432644169271453207/100000000000000000000)
  directionLo := (111730788200421233229/20000000000000000000)
  directionHi := (279326970501053083073/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree127.table
  base := (7104927504793650184199669342972013033713/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-8391239589441450868745331338340000000000000)
      constant := (307646855972398466833725733841036135770792730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree127.table
  base := (8881159380924846669294061804355219519181/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-727523547597163666063174724218020000000000000)
      constant := (26788440066956533527377361409324972459510457464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111730788200421233229/20000000000000000000)
  centralHi := (279326970501053083073/50000000000000000000)
  directionLo := (560866440516066510641/100000000000000000000)
  directionHi := (280433220258033255321/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree128.table
  base := (1817020559062287821108923574137570467631/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2442)
      previous := (0)
      next := (2035)
      square := (58814580193741543903684920660000000000000)
      linear := (-8455400949652805280276623979060000000000000)
      constant := (312438811526303511205653675485065841063334040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree128.table
  base := (72680822362038439787292811158038866202363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (211751)
      previous := (0)
      next := (174640)
      square := (5076038520357379694100674598780000000000000)
      linear := (-733087115240945200869138175473180000000000000)
      constant := (27205702141256243699790891462486919879751276809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell159.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560866440516066510641/100000000000000000000)
  centralHi := (280433220258033255321/50000000000000000000)
  directionLo := (2815351232071853011/500000000000000000)
  directionHi := (563070246414370602201/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree129.table
  base := (148659158778641427683921310461340601089853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4884)
      previous := (0)
      next := (4070)
      square := (117629160387483087807369841320000000000000)
      linear := (-17039124619728319383615833239560000000000000)
      constant := (634535693121927124492046289664942212731872213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree129.table
  base := (148659158777877984104986375089500541101647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (423502)
      previous := (0)
      next := (349280)
      square := (10152077040714759388201349197560000000000000)
      linear := (-1477301365769453471350203253456680000000000000)
      constant := (55252385794760457632750900702647414150724499621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell159.Kernel129
