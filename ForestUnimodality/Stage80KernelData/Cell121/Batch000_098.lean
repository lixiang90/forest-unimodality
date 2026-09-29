import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell121.Parameters
import ForestUnimodality.BinomialMassData.Q4583_8778.Batch000_049
import ForestUnimodality.BinomialMassData.Q4583_8778.Batch050_099
import ForestUnimodality.BinomialMassData.Q2294_4389.Batch000_049
import ForestUnimodality.BinomialMassData.Q2294_4389.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree000.table
  base := (1744022692120568826023685457/50000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (14)
      previous := (7)
      next := (7)
      square := (253774921825399069064133080000000000000)
      linear := (-14662606648164013684043638400000000000)
      constant := (69760907684822753040947418280000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree000.table
  base := (1744022692120568826023685457/50000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (14)
      previous := (7)
      next := (7)
      square := (253774921825399069064133080000000000000)
      linear := (-14662606648164013684043638400000000000)
      constant := (69760907684822753040947418280000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree001.table
  base := (194507391863167954495118505425359558276581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-549701938471415400047699125342968000000000000)
      constant := (76617520198331211047506484533238375785714011949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree001.table
  base := (97170060384735744165707138167794839516509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-3851891491199520930741474163429776000000000000)
      constant := (535864520490698693077405041248142340499999333254) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12487144813449494353/25000000000000000000)
  directionHi := (49948579253797977413/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree002.table
  base := (353618116792168660367982616915587462289/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5503806000000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (698363968696081174354795015251240000000000000)
      linear := (-1498815356497060626384396810316435200000000000)
      constant := (63083455770044459245055050512975510991071101888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree002.table
  base := (112982405859561422769804073651873273795183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-7502032626284529392737144623640176000000000000)
      constant := (314943160288244772388233739936737609776785483249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12487144813449494353/25000000000000000000)
  centralHi := (49948579253797977413/100000000000000000000)
  directionLo := (70637958201988507279/100000000000000000000)
  directionHi := (882974477524856341/1250000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree003.table
  base := (1729439450718261581382254503730782377421/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 611534000000000000000000000000000000000000000
      center := (4280738)
      previous := (2140369)
      next := (2140369)
      square := (77595996521786797150532779472360000000000000)
      linear := (-247560888792682188078001649461412800000000000)
      constant := (4427832806010240326333900615248553481575095256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree003.table
  base := (13807328687523255846347457087618367225753/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 611534000000000000000000000000000000000000000
      center := (4280738)
      previous := (2140369)
      next := (2140369)
      square := (77595996521786797150532779472360000000000000)
      linear := (-247826083585989730105173668530012800000000000)
      constant := (4419637439549411267704822930277971691516817551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70637958201988507279/100000000000000000000)
  centralHi := (882974477524856341/1250000000000000000)
  directionLo := (43256738516729428587/50000000000000000000)
  directionHi := (3460539081338354287/4000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree004.table
  base := (44503819780303978114797739154673127889007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-14786403208856093795098164399944976000000000000)
      constant := (138120846290022603901721090304701388657142030321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree004.table
  base := (44399907235185650572149140640636419548271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-2114616413779220902389783649151568000000000000)
      constant := (19695513836886773754161391195530866980592229959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43256738516729428587/50000000000000000000)
  centralHi := (3460539081338354287/4000000000000000000)
  directionLo := (3995886340303838193/4000000000000000000)
  directionHi := (49948579253797977413/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree005.table
  base := (29942035523105021132051438586164488592589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-18432566422041489126686254574126376000000000000)
      constant := (106720052260895529905205010390637744651411446867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree005.table
  base := (7466745601525780066127096248286690862557/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-18452456031539554778724156004271376000000000000)
      constant := (106566038172886599946860921246000037778972783884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3995886340303838193/4000000000000000000)
  centralHi := (49948579253797977413/50000000000000000000)
  directionLo := (111688418591027998181/100000000000000000000)
  directionHi := (55844209295513999091/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree006.table
  base := (4157895511916859179187830065586930757823/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 611534000000000000000000000000000000000000000
      center := (4280738)
      previous := (2140369)
      next := (2140369)
      square := (77595996521786797150532779472360000000000000)
      linear := (-490638436338375210183874327740172800000000000)
      constant := (2046857526354457583418857538796003857027265241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree006.table
  base := (1295903495559384041536215355625305171449/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-2455844129624951471191091829386864000000000000)
      constant := (10225852479986700393300863887095786981735142128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111688418591027998181/100000000000000000000)
  centralHi := (55844209295513999091/50000000000000000000)
  directionLo := (122348532548770793521/100000000000000000000)
  directionHi := (61174266274385396761/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree007.table
  base := (14625135384990718515260417921318603936247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-3674984692630325684266062131784168000000000000)
      constant := (12517724213447395133457945305754147446852846863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree007.table
  base := (14583354414923505976945199601051030766027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-3678962614529938814673642417813168000000000000)
      constant := (12515959881945826513829790312720886674017428483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122348532548770793521/100000000000000000000)
  centralHi := (61174266274385396761/50000000000000000000)
  directionLo := (66075759523274804349/50000000000000000000)
  directionHi := (132151519046549608699/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree008.table
  base := (10188387317429694641476299120662666073659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-4195865151656810731635789299524368000000000000)
      constant := (12828198013881182010678390470196177250871489011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree008.table
  base := (10155262736655409155708899956287232712919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-29402879436794580164711167384902576000000000000)
      constant := (89840142369859228827974797734954672564379934857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66075759523274804349/50000000000000000000)
  centralHi := (132151519046549608699/100000000000000000000)
  directionLo := (141275916403977014559/100000000000000000000)
  directionHi := (882974477524856341/625000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree009.table
  base := (3405630372091544232124463471898715732253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-3668579919420341161448735030094664000000000000)
      constant := (10754482517578137731622414504141095226607606102) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree009.table
  base := (6783901778195260212151573698430233087531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-3672557841319954291856315316123664000000000000)
      constant := (10764934045619316198207651500925613080475091277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141275916403977014559/100000000000000000000)
  centralHi := (882974477524856341/625000000000000000)
  directionLo := (74922868880696966119/50000000000000000000)
  directionHi := (149845737761393932239/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree010.table
  base := (4130392087832821661613784356257951703557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-36663382487968465784626705445033376000000000000)
      constant := (107602997858449120475315488557273686066873618971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree010.table
  base := (1026761030010526746639696551806521493563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-36703161706964597088702508305323376000000000000)
      constant := (107747696573357707713316097734393047670802001556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74922868880696966119/50000000000000000000)
  centralHi := (149845737761393932239/100000000000000000000)
  directionLo := (31590255266287024507/20000000000000000000)
  directionHi := (19743909541429390317/12500000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree011.table
  base := (485137156610266279281557684255224726423/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 227430000000000000000000000000000000000000000
      center := (1592010)
      previous := (796005)
      next := (796005)
      square := (28858015235375255138627893192200000000000000)
      linear := (-333136741331850091869543765448056000000000000)
      constant := (1005541910369479661056683070185692303812153156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree011.table
  base := (240020549157006568627306434923711569127/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (4122573605053607876946841884600000000000000)
      linear := (-47642624370778755077565736441008000000000000)
      constant := (143880966802655260254073956557785111104748984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31590255266287024507/20000000000000000000)
  centralHi := (19743909541429390317/12500000000000000000)
  directionLo := (165660696196177791069/100000000000000000000)
  directionHi := (16566069619617779107/10000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree012.table
  base := (59940857572283730664073837122740284477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-4883967657148806271978098421488464000000000000)
      constant := (15406416321736875454318368323439465857127357718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree012.table
  base := (2036658755648493559351763469352077973/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 611534000000000000000000000000000000000000000
      center := (4280738)
      previous := (2140369)
      next := (2140369)
      square := (77595996521786797150532779472360000000000000)
      linear := (-977854310602991422504307760572092800000000000)
      constant := (3086859793116762362199703575022079368255702910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165660696196177791069/100000000000000000000)
  centralHi := (16566069619617779107/10000000000000000000)
  directionLo := (173026954066917714349/100000000000000000000)
  directionHi := (3460539081338354287/2000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree013.table
  base := (-1408428759263568720740451017122536090051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-47601872127524651779390975967577576000000000000)
      constant := (158353123581229240161414847950123659566180382947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree013.table
  base := (-284906249549633295907689574886210207801/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5503806000000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (698363968696081174354795015251240000000000000)
      linear := (-9530717022443924494937903937190915200000000000)
      constant := (31732297702232436452037246328099603070521804697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173026954066917714349/100000000000000000000)
  centralHi := (3460539081338354287/2000000000000000000)
  directionLo := (180092163636145452033/100000000000000000000)
  directionHi := (90046081818072726017/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree014.table
  base := (-1348015980384940395613135666475504304823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-7321147905815721015854152305965568000000000000)
      constant := (25802081103168154011286234848546774936298477666) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree014.table
  base := (-338805598926130412269288977601824299209/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-7329103749614947276669312878023568000000000000)
      constant := (25854829083032539036574297715542371320610120312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180092163636145452033/100000000000000000000)
  centralHi := (90046081818072726017/50000000000000000000)
  directionLo := (93445235261918421687/50000000000000000000)
  directionHi := (1495123764190694747/800000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree015.table
  base := (-755966383492336077721289808388873845121/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87362000000000000000000000000000000000000000
      center := (611534)
      previous := (305767)
      next := (305767)
      square := (11085142360255256735790397067480000000000000)
      linear := (-174267296996493468071641766082350400000000000)
      constant := (651874676231332811688163674688131601571269599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree015.table
  base := (-3792739781652474533715232106350040145757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-6105985264709959933186762289597264000000000000)
      constant := (22863808618415890615610998369925827274752319381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93445235261918421687/50000000000000000000)
  centralHi := (1495123764190694747/800000000000000000)
  directionLo := (12090625976042553281/6250000000000000000)
  directionHi := (193450015616680852497/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree016.table
  base := (-4687580359711684684078080623845527166763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-58540361767080837774155246490121776000000000000)
      constant := (232454619383239641468149785317031798253203400011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree016.table
  base := (-293695572814959773722954970003422889509/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-58604008517474647860676531066585776000000000000)
      constant := (232956647123928139196465303359596264641464229968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12090625976042553281/6250000000000000000)
  centralHi := (193450015616680852497/100000000000000000000)
  directionLo := (199794317015191909651/100000000000000000000)
  directionHi := (49948579253797977413/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree017.table
  base := (-2720486683834543654835854640832991855313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-62186524980266233105743336664303176000000000000)
      constant := (261897151325235689034572579378641496428777178722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree017.table
  base := (-2725643823949348861449220024108136151251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-62254149652559656322672201526796176000000000000)
      constant := (262471265566412225680239757899965527601927838694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199794317015191909651/100000000000000000000)
  centralHi := (49948579253797977413/25000000000000000000)
  directionLo := (205943268112944010209/100000000000000000000)
  directionHi := (20594326811294401021/10000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree018.table
  base := (-757180312431871858905049291250676915459/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-7314743132605736493036825204276064000000000000)
      constant := (32624460986863320643014787580507306172726783576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree018.table
  base := (-6066634109723485721041158288185937268819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3057670)
      previous := (1528835)
      next := (1528835)
      square := (55425711801276283678951985337400000000000000)
      linear := (-1046099853772137536264569396619152000000000000)
      constant := (4670955521054950558009487661359606074160717261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205943268112944010209/100000000000000000000)
  centralHi := (20594326811294401021/10000000000000000000)
  directionLo := (211913874605965521839/100000000000000000000)
  directionHi := (2648923432574569023/1250000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree019.table
  base := (-3275624885371832072795640864879381845113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 76230000000000000000000000000000000000000000
      center := (533610)
      previous := (266805)
      next := (266805)
      square := (9672631145375085517379432344200000000000000)
      linear := (-192462192262152420412519437708216000000000000)
      constant := (907435912379839424833200544220442944389407202) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree019.table
  base := (-1639855485962035911570831172185332496427/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 76230000000000000000000000000000000000000000
      center := (533610)
      previous := (266805)
      next := (266805)
      square := (9672631145375085517379432344200000000000000)
      linear := (-192671556572658374644497347499216000000000000)
      constant := (909457672986703429953629737027708841518947916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211913874605965521839/100000000000000000000)
  centralHi := (2648923432574569023/1250000000000000000)
  directionLo := (43544161868147521651/20000000000000000000)
  directionHi := (3401887645949025129/1562500000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree020.table
  base := (-6934200562706654419091250874476030005653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-73125014619822419100507607186847376000000000000)
      constant := (363757310523430136366878629591935509599353492341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree020.table
  base := (-1388289923053103199410842391807633992363/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5503806000000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (698363968696081174354795015251240000000000000)
      linear := (-14640914611562936341731842581485475200000000000)
      constant := (72914172740083436220493316849572980593514283211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43544161868147521651/20000000000000000000)
  centralHi := (3401887645949025129/1562500000000000000)
  directionLo := (223376837182055996363/100000000000000000000)
  directionHi := (55844209295513999091/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree021.table
  base := (-3608069079619641642670584695141839384393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3057670)
      previous := (1528835)
      next := (1528835)
      square := (55425711801276283678951985337400000000000000)
      linear := (-1218590124333457371938026942238552000000000000)
      constant := (6382728564797028041009044114074480627700658734) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree021.table
  base := (-722255409209404213557667226792538694061/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87362000000000000000000000000000000000000000
      center := (611534)
      previous := (305767)
      next := (305767)
      square := (11085142360255256735790397067480000000000000)
      linear := (-243983219659999016414777407516310400000000000)
      constant := (1279406535558849448209515290972156634609442918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223376837182055996363/100000000000000000000)
  centralHi := (55844209295513999091/25000000000000000000)
  directionLo := (228893145286030118801/100000000000000000000)
  directionHi := (114446572643015059401/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree022.table
  base := (-3702653367479323657368094664556946623593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (4122573605053607876946841884600000000000000)
      linear := (-94943732049814887560429501222208000000000000)
      constant := (522580217681946412174142520815444960839892686) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree022.table
  base := (-7410973378854671477305532858305501915471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 227430000000000000000000000000000000000000000
      center := (1592010)
      previous := (796005)
      next := (796005)
      square := (28858015235375255138627893192200000000000000)
      linear := (-665329382875906600269839287833456000000000000)
      constant := (3666265576534759580203422701139429969936443047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228893145286030118801/100000000000000000000)
  centralHi := (114446572643015059401/50000000000000000000)
  directionLo := (117139801656401815113/50000000000000000000)
  directionHi := (234279603312803630227/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree023.table
  base := (-7508630063323385210744133751767915519481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-84063504259378605095271877709391576000000000000)
      constant := (485278891353665521726676224739416195978193677657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree023.table
  base := (-1502725018544131078336559571329455293081/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5503806000000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (698363968696081174354795015251240000000000000)
      linear := (-16830999292613941418929244857611715200000000000)
      constant := (97273411053594051638999103062229639590604516857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117139801656401815113/50000000000000000000)
  centralHi := (234279603312803630227/100000000000000000000)
  directionLo := (119772485465024027179/50000000000000000000)
  directionHi := (239544970930048054359/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree024.table
  base := (-1506386532336235911991749279017282090819/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 611534000000000000000000000000000000000000000
      center := (4280738)
      previous := (2140369)
      next := (2140369)
      square := (77595996521786797150532779472360000000000000)
      linear := (-1949103721612533342819110397412732800000000000)
      constant := (11779026933480463526133493885383381906936546827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree024.table
  base := (-7536327623224357135895081648305883771151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-9756126399794968395182432749807664000000000000)
      constant := (59027089842135704901399978487684310836946472183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119772485465024027179/50000000000000000000)
  centralHi := (239544970930048054359/100000000000000000000)
  directionLo := (122348532548770793521/50000000000000000000)
  directionHi := (244697065097541587043/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree025.table
  base := (-7480119242237085203754954924531092811587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-91355830685749395758448058057754376000000000000)
      constant := (576943909043243394926347527871822762098515299939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree025.table
  base := (-7483979653111359434210675547745794081123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-13065039819034246288376795029782768000000000000)
      constant := (82604987713530792803109276628393443718682196133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122348532548770793521/50000000000000000000)
  centralHi := (244697065097541587043/100000000000000000000)
  directionLo := (31217862033623735883/12500000000000000000)
  directionHi := (49948579253797977413/20000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree026.table
  base := (-3678661237481484686370066505219335965029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-95001993898934791090036148231935776000000000000)
      constant := (625930609756639539130187010402607323399657599626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree026.table
  base := (-3680354000789691461147533362326689473691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-95105419868324732480633235668689776000000000000)
      constant := (627329014908322209712041144201212688514562632054) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31217862033623735883/12500000000000000000)
  centralHi := (49948579253797977413/20000000000000000000)
  directionLo := (254688780291351626251/100000000000000000000)
  directionHi := (63672195072837906563/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree027.table
  base := (-3583512894422535946309157914510859788621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-10960906345791131824624915378457464000000000000)
      constant := (75222969787570196772494584546786773870025445386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree027.table
  base := (-3584995248155815499437493308223730883809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-10972840111489971215847656236544464000000000000)
      constant := (75390726741734048211206904597078596957700746994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254688780291351626251/100000000000000000000)
  centralHi := (63672195072837906563/25000000000000000000)
  directionLo := (259540431100376571523/100000000000000000000)
  directionHi := (64885107775094142881/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree028.table
  base := (-3456083007942524455146837371314042638697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-14613474332186511679030332654328368000000000000)
      constant := (104309168880132033833929464220383507462983374174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree028.table
  base := (-6914758671498866145844613696391453937229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-14629386019784964200660653798444368000000000000)
      constant := (104541346285547722906002270356161308105111100459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259540431100376571523/100000000000000000000)
  centralHi := (64885107775094142881/25000000000000000000)
  directionLo := (66075759523274804349/25000000000000000000)
  directionHi := (264303038093099217397/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree029.table
  base := (-6595219489213331105837410983632169186493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-15134354791212996726400059822068568000000000000)
      constant := (112199451049492329315081713911777610959883193403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree029.table
  base := (-6597483902224520351555238098667136508899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-106055843273579757866620247049320976000000000000)
      constant := (787140863893498867296462517185352795039751315203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66075759523274804349/25000000000000000000)
  centralHi := (264303038093099217397/100000000000000000000)
  directionLo := (67245332790980368579/25000000000000000000)
  directionHi := (268981331163921474317/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree030.table
  base := (-3109137208740781059421614443442950007589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-12176294083519596935154278769851264000000000000)
      constant := (93632989677449432441102185633351679010059068474) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree030.table
  base := (-6220249799169700074338155107738174818067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-12189553823184974036512879723281264000000000000)
      constant := (93840569607235187317577860995908541500404107611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67245332790980368579/25000000000000000000)
  centralHi := (268981331163921474317/100000000000000000000)
  directionLo := (273579635726397098043/100000000000000000000)
  directionHi := (68394908931599274511/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree031.table
  base := (-1156618360439413829577034964643894207803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5503806000000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (698363968696081174354795015251240000000000000)
      linear := (-22646561992972353549595319820568555200000000000)
      constant := (180412317061477795778162351113164666797864300891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree031.table
  base := (-1446203283272051751331494444938089680633/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-113356125543749774790611587969741776000000000000)
      constant := (904057377250979816891997676559549120774388021604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273579635726397098043/100000000000000000000)
  centralHi := (68394908931599274511/25000000000000000000)
  directionLo := (139050959771643673773/50000000000000000000)
  directionHi := (278101919543287347547/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree032.table
  base := (-2645578376011359928788205090279767082831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-116878973178047163079564689277024176000000000000)
      constant := (963486105102493894453396299316498428250912245214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree032.table
  base := (-5292655145990504740785034672100865873139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-16715180954119254750372465489993168000000000000)
      constant := (137944791430965134227985314516914154700158738069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139050959771643673773/50000000000000000000)
  centralHi := (278101919543287347547/100000000000000000000)
  directionLo := (282551832807954029119/100000000000000000000)
  directionHi := (882974477524856341/312500000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree033.table
  base := (-37060326003191766584207478708538551059/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 25270000000000000000000000000000000000000000
      center := (176890)
      previous := (88445)
      next := (88445)
      square := (3206446137263917237625321465800000000000000)
      linear := (-110675056373950925997385472406984000000000000)
      constant := (943036749155131231947792450795692954428660096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree033.table
  base := (-4745024786058469046284092796646291203061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25270000000000000000000000000000000000000000
      center := (176890)
      previous := (88445)
      next := (88445)
      square := (3206446137263917237625321465800000000000000)
      linear := (-110795599461817990555190935619984000000000000)
      constant := (945114947454725900371903891178586822129864853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282551832807954029119/100000000000000000000)
  centralHi := (882974477524856341/312500000000000000)
  directionLo := (143466371314506090917/50000000000000000000)
  directionHi := (57386548525802436367/20000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree034.table
  base := (-4141843001727014915142120468978306570937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-124171299604417953742740869625386976000000000000)
      constant := (1092501422736114227327374856456817215212518756889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree034.table
  base := (-207148757385796963591480935153337522421/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5503806000000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (698363968696081174354795015251240000000000000)
      linear := (-24861309789800960035319719870074595200000000000)
      constant := (218980878504319453568103047773467232848148331348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143466371314506090917/50000000000000000000)
  centralHi := (57386548525802436367/20000000000000000000)
  directionLo := (72811940711190995163/25000000000000000000)
  directionHi := (291247762844763980653/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree035.table
  base := (-3486411389171333912112701404202021195047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-18259637545371907010618422828509768000000000000)
      constant := (165726694625502343124985335492190893609612367937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree035.table
  base := (-3487394189943808247786393101280042151957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-18279527154869972662656324258654768000000000000)
      constant := (166090534381424975811410510658571358308843296547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72811940711190995163/25000000000000000000)
  centralHi := (291247762844763980653/100000000000000000000)
  directionLo := (4617184061217861249/1562500000000000000)
  directionHi := (295499779917943119937/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree036.table
  base := (-555635634808674170009161206725639335251/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87362000000000000000000000000000000000000000
      center := (611534)
      previous := (305767)
      next := (305767)
      square := (11085142360255256735790397067480000000000000)
      linear := (-417344844542186490177514444361110400000000000)
      constant := (3903877051740864049220423901532575748196901069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree036.table
  base := (-694757658476217266360741842967838977491/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-14622981246574979677843326696754864000000000000)
      constant := (136935129090590571136309122923509395117478037612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4617184061217861249/1562500000000000000)
  centralHi := (295499779917943119937/100000000000000000000)
  directionLo := (299691475522787864477/100000000000000000000)
  directionHi := (149845737761393932239/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree037.table
  base := (-63055530099860537748969039041538378243/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-135109789243974139737505140147931176000000000000)
      constant := (1301402905871083576509618481446873831193534514272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree037.table
  base := (-1009257898872176523585476558764946470927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-135256972354259825562585610731004176000000000000)
      constant := (1304249918631320379969512428887816087023633151838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299691475522787864477/100000000000000000000)
  centralHi := (149845737761393932239/50000000000000000000)
  directionLo := (37978168290829168371/12500000000000000000)
  directionHi := (303825346326633346969/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree038.table
  base := (-1205742119864994459294546143183823430623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 76230000000000000000000000000000000000000000
      center := (533610)
      previous := (266805)
      next := (266805)
      square := (9672631145375085517379432344200000000000000)
      linear := (-384365519271910069443471552138816000000000000)
      constant := (3809225195514834267369163834996197713988360871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree038.table
  base := (-15079775082831944016475304575243634043/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15246000000000000000000000000000000000000000
      center := (106722)
      previous := (53361)
      next := (53361)
      square := (1934526229075017103475886468840000000000000)
      linear := (-76956849578584395581485474344163200000000000)
      constant := (763508889867464792299777613927240284443043376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37978168290829168371/12500000000000000000)
  centralHi := (303825346326633346969/100000000000000000000)
  directionLo := (38487965172564745083/12500000000000000000)
  directionHi := (61580744276103592133/20000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree039.table
  base := (-342524308821999907587449694442337111521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-15822457296704992266742368944032664000000000000)
      constant := (161211355582439299127994056045591555908421558393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree039.table
  base := (-34307811552557756676442507946194454959/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87362000000000000000000000000000000000000000
      center := (611534)
      previous := (305767)
      next := (305767)
      square := (11085142360255256735790397067480000000000000)
      linear := (-452562713093428071385958576671190400000000000)
      constant := (4616081934439130339492910536711262160025871842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38487965172564745083/12500000000000000000)
  centralHi := (61580744276103592133/20000000000000000000)
  directionLo := (311928777462812127199/100000000000000000000)
  directionHi := (389910971828515159/125000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree040.table
  base := (11429927872028611092178801847384915813/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5503806000000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (698363968696081174354795015251240000000000000)
      linear := (-29209655776706065146453882134095075200000000000)
      constant := (305743514784236167574782072516497728919805421390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree040.table
  base := (571017402246315533994159084779820791101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-146207395759514850948572622111635376000000000000)
      constant := (1532045666522133257719321381816398683174493215203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311928777462812127199/100000000000000000000)
  centralHi := (389910971828515159/125000000000000000)
  directionLo := (31590255266287024507/10000000000000000000)
  directionHi := (315902552662870245071/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree041.table
  base := (191999930381625136892064015726325937303/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-149694442096715721063857500844656776000000000000)
      constant := (1608575534511571891728756316563253414206735500872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree041.table
  base := (1535585418945260947205029926135788009129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-149857536894599859410568292571845776000000000000)
      constant := (1612072239523599833074469729959478789429686122487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31590255266287024507/10000000000000000000)
  centralHi := (315902552662870245071/100000000000000000000)
  directionLo := (79956739611332345099/25000000000000000000)
  directionHi := (319826958445329380397/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree042.table
  base := (637678625637792995004542400457662825551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3057670)
      previous := (1528835)
      next := (1528835)
      square := (55425711801276283678951985337400000000000000)
      linear := (-2433977862061922482467390333632352000000000000)
      constant := (26832941874158354659967199868670788679531572924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree042.table
  base := (510071369369157104453738306217247698849/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87362000000000000000000000000000000000000000
      center := (611534)
      previous := (305767)
      next := (305767)
      square := (11085142360255256735790397067480000000000000)
      linear := (-487325961998999580547822104863670400000000000)
      constant := (5378237421744148540527484631398048396733423169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79956739611332345099/25000000000000000000)
  centralHi := (319826958445329380397/100000000000000000000)
  directionLo := (323703790397739062361/100000000000000000000)
  directionHi := (161851895198869531181/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree043.table
  base := (451926697303793448432298957208863504251/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-22426681217583787389576240170431368000000000000)
      constant := (253488051026563122833290889831817120404501531032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree043.table
  base := (903776197962180597455985176132710520371/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-157157819164769876334559633492266576000000000000)
      constant := (1778262687109001949689089465452911865916562064052) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323703790397739062361/100000000000000000000)
  centralHi := (161851895198869531181/50000000000000000000)
  directionLo := (327534737833006533919/100000000000000000000)
  directionHi := (2047092111456290837/625000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree044.table
  base := (2364952194027599311483027250174067843687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 227430000000000000000000000000000000000000000
      center := (1592010)
      previous := (796005)
      next := (796005)
      square := (28858015235375255138627893192200000000000000)
      linear := (-1327544890382412455029931994770256000000000000)
      constant := (15375190600911631652087324138953321649937946882) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree044.table
  base := (4729637937431940727657360434428909605073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 227430000000000000000000000000000000000000000
      center := (1592010)
      previous := (796005)
      next := (796005)
      square := (28858015235375255138627893192200000000000000)
      linear := (-1328991407436817229723597553326256000000000000)
      constant := (15408474469569207520390277526705560691148175239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327534737833006533919/100000000000000000000)
  centralHi := (2047092111456290837/625000000000000000)
  directionLo := (331321392392355582139/100000000000000000000)
  directionHi := (16566069619617779107/5000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree045.table
  base := (736753095795322189644334661191527413497/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-18253232772161922487801095726820264000000000000)
      constant := (216491112042505475866765133657134328101141897592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree045.table
  base := (2946897483007900652131669706600455136531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-18273122381659988139838997156965264000000000000)
      constant := (216959168338410212128940224272400682731463348554) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331321392392355582139/100000000000000000000)
  centralHi := (16566069619617779107/5000000000000000000)
  directionLo := (67013051154616798909/20000000000000000000)
  directionHi := (167532627886541997273/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree046.table
  base := (710763794851446073991400691317757565229/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5503806000000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (698363968696081174354795015251240000000000000)
      linear := (-33585051632528539544359590343112755200000000000)
      constant := (407696363567819873412283035851098673194052761574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree046.table
  base := (888429981883868418910441164791362472583/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-24015463224289271674363806410413968000000000000)
      constant := (291840517924521248969984162112833596299872657656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67013051154616798909/20000000000000000000)
  centralHi := (167532627886541997273/50000000000000000000)
  directionLo := (84691936671885688601/25000000000000000000)
  directionHi := (67753549337508550881/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree047.table
  base := (4185314295716987958451543585387356213789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-171571421375828093053386041889745176000000000000)
      constant := (2130583173666998408366587149446154485453589180934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree047.table
  base := (523153619425341875706655788835177697973/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-171758383705109910182542315333108176000000000000)
      constant := (2135178426469554575495067822577189184201359881904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84691936671885688601/25000000000000000000)
  centralHi := (67753549337508550881/20000000000000000000)
  directionLo := (17121510357239812779/5000000000000000000)
  directionHi := (342430207144796255581/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree048.table
  base := (302590606827868227003119272564786267779/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-19468620509890387598330459118214064000000000000)
      constant := (247191534241155366297414704526850336087679407776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree048.table
  base := (2420688105944230365344803469868620793587/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-19489836093354990960504220643702064000000000000)
      constant := (247724072433822734087185578861946586296770864916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17121510357239812779/5000000000000000000)
  centralHi := (342430207144796255581/100000000000000000000)
  directionLo := (173026954066917714349/50000000000000000000)
  directionHi := (346053908133835428699/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree049.table
  base := (552218419486896032058939704104442878227/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 786258000000000000000000000000000000000000000
      center := (5503806)
      previous := (2751903)
      next := (2751903)
      square := (99766281242297310622113573607320000000000000)
      linear := (-5110392794348539534758920635374513600000000000)
      constant := (66311528445237560323657224566264482497098009132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree049.table
  base := (2761060462227495657612075571952298276613/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-25579809425039989586647665179075568000000000000)
      constant := (332271153910294490125872465287824012276746368308) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173026954066917714349/50000000000000000000)
  centralHi := (346053908133835428699/100000000000000000000)
  directionLo := (34964005477658584189/10000000000000000000)
  directionHi := (349640054776585841891/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree050.table
  base := (12454966315362402696387581628127154932309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-26072844430769182721164330344612768000000000000)
      constant := (345588863643157383457279302618251400291383704861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree050.table
  base := (12454857427692004430468955870664973809659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-182708807110364935568529326713739376000000000000)
      constant := (2424322513655767813221041209657595353421722031077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34964005477658584189/10000000000000000000)
  centralHi := (349640054776585841891/100000000000000000000)
  directionLo := (353189791009942536399/100000000000000000000)
  directionHi := (882974477524856341/250000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree051.table
  base := (2782926968592261323214667645674990795449/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 611534000000000000000000000000000000000000000
      center := (4280738)
      previous := (2140369)
      next := (2140369)
      square := (77595996521786797150532779472360000000000000)
      linear := (-4136801649523770541771964501921572800000000000)
      constant := (55986206607702313397620653817733375710552054383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree051.table
  base := (13914541183212200265277864304713268737279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-20706549805049993781169444130438864000000000000)
      constant := (280532200134298781048681162835255806041991587993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353189791009942536399/100000000000000000000)
  centralHi := (882974477524856341/250000000000000000)
  directionLo := (356704203848398489013/100000000000000000000)
  directionHi := (178352101924199244507/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree052.table
  base := (15423324760058941252791736208319094090543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-189802237441755069711326492760652176000000000000)
      constant := (2621675115688862375508200282569507411985047553329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree052.table
  base := (15423244229582029727438693147961339828439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-190009089380534952492520667634160176000000000000)
      constant := (2627299805501601747519529753533965646957900769417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356704203848398489013/100000000000000000000)
  centralHi := (178352101924199244507/50000000000000000000)
  directionLo := (360184327272290904067/100000000000000000000)
  directionHi := (90046081818072726017/25000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree053.table
  base := (16980994562507346814100460813442407732757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-193448400654940465042914582934833576000000000000)
      constant := (2726009386313487219050066317342376260166997186571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree053.table
  base := (3396185069288266909376733192963116002213/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 786258000000000000000000000000000000000000000
      center := (5503806)
      previous := (2751903)
      next := (2751903)
      square := (99766281242297310622113573607320000000000000)
      linear := (-5533120871874856027271895374124873600000000000)
      constant := (78052926088573519624038992843747033630833994477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360184327272290904067/100000000000000000000)
  centralHi := (90046081818072726017/25000000000000000000)
  directionLo := (90907786445271596317/25000000000000000000)
  directionHi := (363631145781086385269/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree054.table
  base := (72607848621557040561017656124140312293/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-21899395985347317819389185901001664000000000000)
      constant := (314709112543900087153886825409531578782436795136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree054.table
  base := (9293774888492195696693242261231020821821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-21923263516744996601834667617175664000000000000)
      constant := (315383058706305045217112856969229827087251483414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90907786445271596317/25000000000000000000)
  centralHi := (363631145781086385269/100000000000000000000)
  directionLo := (367045597646312380563/100000000000000000000)
  directionHi := (91761399411578095141/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree055.table
  base := (20243139293408224640956385143577622248807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 227430000000000000000000000000000000000000000
      center := (1592010)
      previous := (796005)
      next := (796005)
      square := (28858015235375255138627893192200000000000000)
      linear := (-1659014273399266576083394737877656000000000000)
      constant := (24304073671042919507521480995517515862804617601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree055.table
  base := (20243088214457629869201412291375710711089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 227430000000000000000000000000000000000000000
      center := (1592010)
      previous := (796005)
      next := (796005)
      square := (28858015235375255138627893192200000000000000)
      linear := (-1660822419717272544450476686072656000000000000)
      constant := (24356074963820457332390206260470437788702297127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367045597646312380563/100000000000000000000)
  centralHi := (91761399411578095141/25000000000000000000)
  directionLo := (92607144473648594367/25000000000000000000)
  directionHi := (370428577894594377469/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree056.table
  base := (10973779902414536817876832706687177903707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-29198127184928093005382693351053968000000000000)
      constant := (435891717386268840436374219028775535124212858406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree056.table
  base := (219475159475763785979122293866024216511/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 786258000000000000000000000000000000000000000
      center := (5503806)
      previous := (2751903)
      next := (2751903)
      square := (99766281242297310622113573607320000000000000)
      linear := (-5845990112024999609728667127857193600000000000)
      constant := (87364713482674415903491101690361278284255058380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92607144473648594367/25000000000000000000)
  centralHi := (370428577894594377469/100000000000000000000)
  directionLo := (373780941047673686749/100000000000000000000)
  directionHi := (1495123764190694747/400000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree057.table
  base := (11850424892257333855239269783746367121069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (8470)
      previous := (4235)
      next := (4235)
      square := (153533827704366436783800513400000000000000)
      linear := (-9147124544153455848800375659832000000000000)
      constant := (139107825600704691150935678306680620843298698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree057.table
  base := (2962601517492736988884024777307446203043/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8470000000000000000000000000000000000000000
      center := (59290)
      previous := (29645)
      next := (29645)
      square := (1074736793930565057486603593800000000000000)
      linear := (-64099659912576175685595266215824000000000000)
      constant := (975834772185590907592894101307163255471819368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373780941047673686749/100000000000000000000)
  centralHi := (1495123764190694747/400000000000000000)
  directionLo := (75420700728634827423/20000000000000000000)
  directionHi := (94275875910793534279/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree058.table
  base := (6375747881115902672538798768523925497053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-211679216720867441700855033805740576000000000000)
      constant := (3278254633264325817645326532606045272588466567436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree058.table
  base := (25502959222447234195760240502658787682639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-211909936191045003264494690395422576000000000000)
      constant := (3285251631085938127203747731376140993800217312017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75420700728634827423/20000000000000000000)
  centralHi := (94275875910793534279/25000000000000000000)
  directionLo := (380397046557186596959/100000000000000000000)
  directionHi := (2377481540982416231/625000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree059.table
  base := (27353970090396771719950519531714261917763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-215325379934052837032443123979921976000000000000)
      constant := (3394818047488691420416600929316112746514277752989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree059.table
  base := (6838485595238777724928582887010236716913/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-215560077326130011726490360855632976000000000000)
      constant := (3402058299891395531658075425316472589807932141756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380397046557186596959/100000000000000000000)
  centralHi := (2377481540982416231/625000000000000000)
  directionLo := (38366231714738851211/10000000000000000000)
  directionHi := (383662317147388512111/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree060.table
  base := (14626886443650962454652949396072047148991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-24330171460804248040447912683789264000000000000)
      constant := (390379942849963518854960822212083763281211062194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree060.table
  base := (29253749124308981888983013657999143861541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3057670)
      previous := (1528835)
      next := (1528835)
      square := (55425711801276283678951985337400000000000000)
      linear := (-3479527277162143177595016370092752000000000000)
      constant := (55887415029728665156514961883782580603015972421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38366231714738851211/10000000000000000000)
  centralHi := (383662317147388512111/100000000000000000000)
  directionLo := (386900031233361704993/100000000000000000000)
  directionHi := (193450015616680852497/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree061.table
  base := (15601194646513854958102526853446494795207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-222617706360423627695619304328284776000000000000)
      constant := (3634058918516136370500190319746395484732829057842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree061.table
  base := (6240473784016187619218257975397310565117/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5503806000000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (698363968696081174354795015251240000000000000)
      linear := (-44572071919260005730096340355210755200000000000)
      constant := (728359628609249857312867520982934156336077167651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386900031233361704993/100000000000000000000)
  centralHi := (193450015616680852497/50000000000000000000)
  directionLo := (195055437464486747233/50000000000000000000)
  directionHi := (390110874928973494467/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree062.table
  base := (33199810349268292969442330867004643176479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-226263869573609023027207394502466176000000000000)
      constant := (3756736321435696823960747537595970510571282089537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree062.table
  base := (16599896443717588207988347554359999450801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-226510500731385037112477372236264176000000000000)
      constant := (3764731263972226987697529731139720243137315248606) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195055437464486747233/50000000000000000000)
  centralHi := (390110874928973494467/100000000000000000000)
  directionLo := (393295506340108262207/100000000000000000000)
  directionHi := (6145242286564191597/1562500000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree063.table
  base := (17623014250474786734252046147038705024037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3057670)
      previous := (1528835)
      next := (1528835)
      square := (55425711801276283678951985337400000000000000)
      linear := (-3649365599790387592996753725026152000000000000)
      constant := (61610344025674951546213710659742881348309920394) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree063.table
  base := (17623006769075611468960883825636538860409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3057670)
      previous := (1528835)
      next := (1528835)
      square := (55425711801276283678951985337400000000000000)
      linear := (-3653343521690000723404334011055152000000000000)
      constant := (61741372841967978118153870830849755307923051058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393295506340108262207/100000000000000000000)
  centralHi := (6145242286564191597/1562500000000000000)
  directionLo := (198227278569824413047/50000000000000000000)
  directionHi := (79290911427929765219/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree064.table
  base := (18670518688217878936540830826782328098083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-33365170857139973384340510692975568000000000000)
      constant := (572600708218212583671626136331260091725742543414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree064.table
  base := (373410245582553726246897423743955635803/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5503806000000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (698363968696081174354795015251240000000000000)
      linear := (-46762156600311010807293742631336995200000000000)
      constant := (803344760177214601397948606570776563720663662180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198227278569824413047/50000000000000000000)
  centralHi := (79290911427929765219/20000000000000000000)
  directionLo := (399588634030383819303/100000000000000000000)
  directionHi := (49948579253797977413/12500000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree065.table
  base := (39484831602162567208773030635527534361487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-237202359213165209021971665025010376000000000000)
      constant := (4136996158378067578828011275986882218391979159761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree065.table
  base := (3948482062389290169915318182269953298647/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5503806000000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (698363968696081174354795015251240000000000000)
      linear := (-47492184827328012499692876723379075200000000000)
      constant := (829156636969553271681845783230994110584813150482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399588634030383819303/100000000000000000000)
  centralHi := (49948579253797977413/12500000000000000000)
  directionLo := (100674580026359233199/25000000000000000000)
  directionHi := (402698320105436932797/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree066.table
  base := (10419351661576199789998184209919553475827/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25270000000000000000000000000000000000000000
      center := (176890)
      previous := (88445)
      next := (88445)
      square := (3206446137263917237625321465800000000000000)
      linear := (-221164850712902299681873053442784000000000000)
      constant := (3919031463450979850379689766604450846533659316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree066.table
  base := (8335479449214406786899686673018227362441/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5054000000000000000000000000000000000000000
      center := (35378)
      previous := (17689)
      next := (17689)
      square := (641289227452783447525064293160000000000000)
      linear := (-44281187377727285759496795973756800000000000)
      constant := (785470087892707573871121091116681860544888407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100674580026359233199/25000000000000000000)
  centralHi := (402698320105436932797/100000000000000000000)
  directionLo := (202892088057428873913/50000000000000000000)
  directionHi := (405784176114857747827/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree067.table
  base := (21959379343465281031653066654795796862367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-244494685639535999685147845373373176000000000000)
      constant := (4400692262970050681943514798591587797545876668802) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree067.table
  base := (4391875063975251260806183838681345888457/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 786258000000000000000000000000000000000000000
      center := (5503806)
      previous := (2751903)
      next := (2751903)
      square := (99766281242297310622113573607320000000000000)
      linear := (-6993177325908859412070163558209033600000000000)
      constant := (126000803475831100381455743361344112855566423906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202892088057428873913/50000000000000000000)
  centralHi := (405784176114857747827/100000000000000000000)
  directionLo := (10221168541154150579/2500000000000000000)
  directionHi := (408846741646166023161/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree068.table
  base := (46208884500806804922220037387001508032803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-248140848852721395016735935547554576000000000000)
      constant := (4535597147323843750731706625428074058959994674109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree068.table
  base := (46208877613461493986524589333043608952347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-248411347541895087884451394997526576000000000000)
      constant := (4545213655300029986189067719238564434606790566341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10221168541154150579/2500000000000000000)
  centralHi := (408846741646166023161/100000000000000000000)
  directionLo := (411886536225888020419/100000000000000000000)
  directionHi := (20594326811294401021/5000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree069.table
  base := (6068472671202688174235725481994227905489/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-27976334673989643372036002857970664000000000000)
      constant := (519171101030996139356300602336220658671821240504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree069.table
  base := (4854777547621803463652770406443004560927/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 611534000000000000000000000000000000000000000
      center := (4280738)
      previous := (2140369)
      next := (2140369)
      square := (77595996521786797150532779472360000000000000)
      linear := (-5601366415044002141032157010171932800000000000)
      constant := (104054249380184413934789190286192583551161932018) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411886536225888020419/100000000000000000000)
  centralHi := (20594326811294401021/5000000000000000000)
  directionLo := (2593150377177831049/625000000000000000)
  directionHi := (414904060348452967841/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree070.table
  base := (5093544700089452163943506228306562527871/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 786258000000000000000000000000000000000000000
      center := (5503806)
      previous := (2751903)
      next := (2751903)
      square := (99766281242297310622113573607320000000000000)
      linear := (-7298090722259776733711774739883353600000000000)
      constant := (137472015500763777502905822862416733240038796718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree070.table
  base := (2037417678362085871340215953513497626601/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 786258000000000000000000000000000000000000000
      center := (5503806)
      previous := (2751903)
      next := (2751903)
      square := (99766281242297310622113573607320000000000000)
      linear := (-7306046566059002994526935311941353600000000000)
      constant := (137763166166711689134671361273921831042240122645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2593150377177831049/625000000000000000)
  centralHi := (414904060348452967841/100000000000000000000)
  directionLo := (417899796438219912167/100000000000000000000)
  directionHi := (52237474554777489021/12500000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree071.table
  base := (5337187946127640194509997618424551806979/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 786258000000000000000000000000000000000000000
      center := (5503806)
      previous := (2751903)
      next := (2751903)
      square := (99766281242297310622113573607320000000000000)
      linear := (-7402266814065073743185720173431393600000000000)
      constant := (141501115478478699134206540353708362854651694582) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree071.table
  base := (53371875148829959877295722387617795900613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-259361770947150113270438406378157776000000000000)
      constant := (4963022431215102626364417640190567391392284616539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417899796438219912167/100000000000000000000)
  centralHi := (52237474554777489021/12500000000000000000)
  directionLo := (84174841949974239961/20000000000000000000)
  directionHi := (210437104874935599903/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree072.table
  base := (55857077120294807662100629849034518284349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-29191722411718108482565366249364464000000000000)
      constant := (566177266939125589483187484580916425552250540683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree072.table
  base := (89371317491928578248858413690972334343/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 611534000000000000000000000000000000000000000
      center := (4280738)
      previous := (2140369)
      next := (2140369)
      square := (77595996521786797150532779472360000000000000)
      linear := (-5844709157383002705165201707519292800000000000)
      constant := (113475023640217669237937034834552615819382010125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84174841949974239961/20000000000000000000)
  centralHi := (210437104874935599903/50000000000000000000)
  directionLo := (211913874605965521839/50000000000000000000)
  directionHi := (423827749211931043679/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree073.table
  base := (14597759650728030746622592452000158827251/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-266371664918648371674676386418461576000000000000)
      constant := (5240689620858889579512350939207460750308754034612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree073.table
  base := (29195517724910529514165704730660161021153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-266662053217320130194429747298578576000000000000)
      constant := (5251771709876103249629706647248489986189188008318) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211913874605965521839/50000000000000000000)
  centralHi := (423827749211931043679/100000000000000000000)
  directionLo := (426760848217739455193/100000000000000000000)
  directionHi := (213380424108869727597/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree074.table
  base := (7621720343689267525381225127821701367689/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-270017828131833767006264476592642976000000000000)
      constant := (5387821693775886475134084247452604851670779697336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree074.table
  base := (12194752010827426370146557599932905384059/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 786258000000000000000000000000000000000000000
      center := (5503806)
      previous := (2751903)
      next := (2751903)
      square := (99766281242297310622113573607320000000000000)
      linear := (-7723205552925861104469297650251113600000000000)
      constant := (154263124750233497270041965482552637560729730611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426760848217739455193/100000000000000000000)
  centralHi := (213380424108869727597/50000000000000000000)
  directionLo := (214836962683913746749/50000000000000000000)
  directionHi := (429673925367827493499/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree075.table
  base := (6360524858216587731021414879091982151109/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 611534000000000000000000000000000000000000000
      center := (4280738)
      previous := (2140369)
      next := (2140369)
      square := (77595996521786797150532779472360000000000000)
      linear := (-6081422029889314718618945928151652800000000000)
      constant := (123044258189154195143085226172608446212796291206) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree075.table
  base := (63605246278480260275588712431120289704771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-30440259498610016346491232024333264000000000000)
      constant := (616521003366124821800343534340467157622158714357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214836962683913746749/50000000000000000000)
  centralHi := (429673925367827493499/100000000000000000000)
  directionLo := (27035461572955892867/6250000000000000000)
  directionHi := (432567385167294285873/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree076.table
  base := (13257099055230578928173678739888062141163/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15246000000000000000000000000000000000000000
      center := (106722)
      previous := (53361)
      next := (53361)
      square := (1934526229075017103475886468840000000000000)
      linear := (-153634434658285073501075156200003200000000000)
      constant := (3151357004319951444744238729574761897702085549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree076.table
  base := (66285493307588214089191703141395402855517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 76230000000000000000000000000000000000000000
      center := (533610)
      previous := (266805)
      next := (266805)
      square := (9672631145375085517379432344200000000000000)
      linear := (-769009630533449184433287420164016000000000000)
      constant := (15790057340009511489675300400277193155967606091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27035461572955892867/6250000000000000000)
  centralHi := (432567385167294285873/100000000000000000000)
  directionLo := (43544161868147521651/10000000000000000000)
  directionHi := (435441618681475216511/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree077.table
  base := (17253625533995057871542832385412927391717/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (4122573605053607876946841884600000000000000)
      linear := (-331707577061853545455760032013208000000000000)
      constant := (6896629297188515389903293025873152404382754132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree077.table
  base := (69014500454077126359526582283621030460871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (4122573605053607876946841884600000000000000)
      linear := (-332069206325454739129176421652208000000000000)
      constant := (6911185800131628611096493901103420727967369879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43544161868147521651/10000000000000000000)
  centralHi := (435441618681475216511/100000000000000000000)
  directionLo := (219148502076455113051/50000000000000000000)
  directionHi := (438297004152910226103/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree078.table
  base := (35896134287565377724792531813710019951179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3057670)
      previous := (1528835)
      next := (1528835)
      square := (55425711801276283678951985337400000000000000)
      linear := (-4517499698167862671946299004593152000000000000)
      constant := (95186166391450492979359051100889950762974899798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree078.table
  base := (35896133569194023081220537895658478002791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-31656973210305019167156455511070064000000000000)
      constant := (667708894178266748661767229200825243686958791394) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219148502076455113051/50000000000000000000)
  centralHi := (438297004152910226103/100000000000000000000)
  directionLo := (441133907582367943393/100000000000000000000)
  directionHi := (220566953791183971697/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree079.table
  base := (9327349262374259798602990752820778655027/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-288248644197760743664204927463549976000000000000)
      constant := (6154049795264518114158023624258088467944838131048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree079.table
  base := (9327349108984750823062519941028091762903/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-288562900027830180966403770059840976000000000000)
      constant := (6167027723077469514266325046992914214452864435272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441133907582367943393/100000000000000000000)
  centralHi := (220566953791183971697/50000000000000000000)
  directionLo := (221976341638226211789/50000000000000000000)
  directionHi := (443952683276452423579/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree080.table
  base := (77494078290469424604367523285689846654377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-291894807410946138995793017637731376000000000000)
      constant := (6313408951380262828673462138348054626077720029431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree080.table
  base := (774940772425625367226414571924852222939/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5503806000000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (698363968696081174354795015251240000000000000)
      linear := (-58442608232583037885679888104010275200000000000)
      constant := (1265343479599390892219688044851768668137250058340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221976341638226211789/50000000000000000000)
  centralHi := (443952683276452423579/100000000000000000000)
  directionLo := (446753674364111992727/100000000000000000000)
  directionHi := (55844209295513999091/12500000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree081.table
  base := (20104530199455905595551223831494010778137/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-32837885624903503814153456423545864000000000000)
      constant := (719422883337853292311848206502130190774394464316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree081.table
  base := (20104529975773465289520735000434432659783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3057670)
      previous := (1528835)
      next := (1528835)
      square := (55425711801276283678951985337400000000000000)
      linear := (-4696240988857145998260239856829552000000000000)
      constant := (102991255101698225289428223384967457812047924892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446753674364111992727/100000000000000000000)
  centralHi := (55844209295513999091/12500000000000000000)
  directionLo := (112384303321045449179/25000000000000000000)
  directionHi := (449537213284181796717/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree082.table
  base := (16678184264890198367444073938516418861329/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5503806000000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (698363968696081174354795015251240000000000000)
      linear := (-59837426767463385931793839597218835200000000000)
      constant := (1327648158085907692052929862081389659013747859087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree082.table
  base := (667127364484993776333275324678565170869/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5503806000000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (698363968696081174354795015251240000000000000)
      linear := (-59902664686617041270478156288094435200000000000)
      constant := (1330444548500336417460909470718691392635247842675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112384303321045449179/25000000000000000000)
  centralHi := (449537213284181796717/100000000000000000000)
  directionLo := (226151811122960549991/50000000000000000000)
  directionHi := (452303622245921099983/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree083.table
  base := (43206239810118614279691852290240593489687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-302833297050502324990557288160275576000000000000)
      constant := (6803713471858549012398633041497405657892100248722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree083.table
  base := (86412478968258728410690971617305555300281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-303163464568170214814386451900682576000000000000)
      constant := (6818038410601605352185276326515033177547509184743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226151811122960549991/50000000000000000000)
  centralHi := (452303622245921099983/100000000000000000000)
  directionLo := (227526606832175690423/50000000000000000000)
  directionHi := (455053213664351380847/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree084.table
  base := (89482795474276043262662881795370165640301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3057670)
      previous := (1528835)
      next := (1528835)
      square := (55425711801276283678951985337400000000000000)
      linear := (-4864753337518852703526117116419952000000000000)
      constant := (110654349107100279952436280679771212205333987981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree084.table
  base := (44741397458924243758688293787497705955337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3057670)
      previous := (1528835)
      next := (1528835)
      square := (55425711801276283678951985337400000000000000)
      linear := (-4870057233385003544069557497791952000000000000)
      constant := (110887239287840514690108144765620302587670150994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227526606832175690423/50000000000000000000)
  centralHi := (455053213664351380847/100000000000000000000)
  directionLo := (457786290572060237603/100000000000000000000)
  directionHi := (114446572643015059401/25000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree085.table
  base := (92601868708726669816225086237430313654397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-44303660496696159379104781215519768000000000000)
      constant := (1020110336515206256605924288288550571776639438213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree085.table
  base := (92601868233913855309567114343847153613591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-310463746838340231738377792821103376000000000000)
      constant := (7155795735615820348273116334856212173570701913673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457786290572060237603/100000000000000000000)
  centralHi := (114446572643015059401/25000000000000000000)
  directionLo := (460503147009007643871/100000000000000000000)
  directionHi := (14390723344031488871/3125000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree086.table
  base := (11971212396704192804750545638086411963709/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-313771786690058510985321558682819776000000000000)
      constant := (7312358557023264318770221405366607986737333505816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree086.table
  base := (4788484938426029868484408688039893685589/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5503806000000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (698363968696081174354795015251240000000000000)
      linear := (-62822777594685048040074692656262755200000000000)
      constant := (1465547478328021691415551957278273041412213703468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460503147009007643871/100000000000000000000)
  centralHi := (14390723344031488871/3125000000000000000)
  directionLo := (463204068391753920499/100000000000000000000)
  directionHi := (926408136783507841/200000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree087.table
  base := (6186642921409839555620460252599580908627/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-35268661100360434035212183206333464000000000000)
      constant := (831775844183314523675966785199413354891010430544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree087.table
  base := (98986286396959538498196175755116305882261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-35307114345390027629152125971280464000000000000)
      constant := (833524560318181022059065985632569175500701299187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463204068391753920499/100000000000000000000)
  centralHi := (926408136783507841/200000000000000000)
  directionLo := (465889331863421810557/100000000000000000000)
  directionHi := (232944665931710905279/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree088.table
  base := (10225163130889094445271393755075296560319/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45486000000000000000000000000000000000000000
      center := (318402)
      previous := (159201)
      next := (159201)
      square := (5771603047075051027725578638440000000000000)
      linear := (-530684484489965787848756593439971200000000000)
      constant := (12663875168913669031946994730693396539342670034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree088.table
  base := (102251631014103708963513944445663148050779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (4122573605053607876946841884600000000000000)
      linear := (-379473636651234069804444869187408000000000000)
      constant := (9064635996454643859798562175587543568016980971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465889331863421810557/100000000000000000000)
  centralHi := (232944665931710905279/50000000000000000000)
  directionLo := (117139801656401815113/25000000000000000000)
  directionHi := (468559206625607260453/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree089.table
  base := (105565732782751167965007460070291101844031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-324710276329614696980085829205363976000000000000)
      constant := (7839344195404732425133048859237350048037894440993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree089.table
  base := (10556573253133675142340870271029352028017/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5503806000000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (698363968696081174354795015251240000000000000)
      linear := (-65012862275736053117272094932388995200000000000)
      constant := (1571162865959321457922392451283836762667912132702) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117139801656401815113/25000000000000000000)
  centralHi := (468559206625607260453/100000000000000000000)
  directionLo := (471213954253364038209/100000000000000000000)
  directionHi := (47121395425336403821/10000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree090.table
  base := (27232147772089773854728549962541481961757/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-36484048838088899145741546597727264000000000000)
      constant := (891009083564131357336122824912680045260002210476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree090.table
  base := (27232147718490752680025036642417522044583/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-36523828057085030449817349458017264000000000000)
      constant := (892880440561849535789297006657897273852024040644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471213954253364038209/100000000000000000000)
  centralHi := (47121395425336403821/10000000000000000000)
  directionLo := (94770765798861073521/20000000000000000000)
  directionHi := (236926914497152683803/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree091.table
  base := (56170103080914773467111897059428404902791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-47428943250855069663323144221960968000000000000)
      constant := (1171551021004901902690887281293968576782058646078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree091.table
  base := (7021262873688985931355025530042834293431/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-47480656235550040358621687940337968000000000000)
      constant := (1174010799229134668346846208116120598447075769584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94770765798861073521/20000000000000000000)
  centralHi := (236926914497152683803/50000000000000000000)
  directionLo := (476479078052790615899/100000000000000000000)
  directionHi := (4764790780527906159/1000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree092.table
  base := (115800577949307309307071912038046751456189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-47949823709881554710692871389701168000000000000)
      constant := (1197810054303988772969287375734481697353220125381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree092.table
  base := (2895014444836399487493623702054382796161/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5503806000000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (698363968696081174354795015251240000000000000)
      linear := (-67202946956787058194469497208515235200000000000)
      constant := (1680453843658494690456983517452196343839230755064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476479078052790615899/100000000000000000000)
  centralHi := (4764790780527906159/1000000000000000000)
  directionLo := (119772485465024027179/25000000000000000000)
  directionHi := (479089941860096108717/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree093.table
  base := (119309706405395256146610066379679320482717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-37699436575817364256270909989121064000000000000)
      constant := (952280161248119778173905809212949528786038928939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree093.table
  base := (59654853136269836824820866342530520748117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-37740541768780033270482572944754064000000000000)
      constant := (954278315111019241858929658728034851475178981478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119772485465024027179/25000000000000000000)
  centralHi := (479089941860096108717/100000000000000000000)
  directionLo := (96337330866281157813/20000000000000000000)
  directionHi := (240843327165702894533/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree094.table
  base := (3071689787295717846567185460079021478151/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5503806000000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (698363968696081174354795015251240000000000000)
      linear := (-68588218479108334727605256015254195200000000000)
      constant := (1751682072048896485425975212760109152342305370824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree094.table
  base := (122867591378588967275812962889697714194443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-343315017054105307896338826962996976000000000000)
      constant := (8776782447620333937807673745845559232784830275029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96337330866281157813/20000000000000000000)
  centralHi := (240843327165702894533/50000000000000000000)
  directionLo := (242134721555199588607/50000000000000000000)
  directionHi := (96853888622079835443/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree095.table
  base := (63237116588178750772549742342478567696597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 76230000000000000000000000000000000000000000
      center := (533610)
      previous := (266805)
      next := (266805)
      square := (9672631145375085517379432344200000000000000)
      linear := (-960075500301183016536327895430616000000000000)
      constant := (24787637415715748786376311701514398243102317862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree095.table
  base := (126474233079848278819979045799209161081919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (76230)
      previous := (38115)
      next := (38115)
      square := (1381804449339297931054204620600000000000000)
      linear := (-137303188836244683956602492055088000000000000)
      constant := (3548516839362313991040705877565898776418209791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242134721555199588607/50000000000000000000)
  centralHi := (96853888622079835443/20000000000000000000)
  directionLo := (486838529802160464581/100000000000000000000)
  directionHi := (243419264901080232291/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree096.table
  base := (3253240785795077861853955021906594099109/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 611534000000000000000000000000000000000000000
      center := (4280738)
      previous := (2140369)
      next := (2140369)
      square := (77595996521786797150532779472360000000000000)
      linear := (-7782964862709165873360054676102972800000000000)
      constant := (203117815369888756647721020464651865263218092824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree096.table
  base := (130129631349561689903000556235189498515151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (387979982608933985752663897361800000000000000)
      linear := (-38957255480475036091147796431490864000000000000)
      constant := (1017718183585582670814625336363998211392482175817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486838529802160464581/100000000000000000000)
  centralHi := (243419264901080232291/50000000000000000000)
  directionLo := (122348532548770793521/25000000000000000000)
  directionHi := (97878826039016634817/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree097.table
  base := (66916893117631808187928626464506936326209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27519030000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (3491819843480405871773975076256200000000000000)
      linear := (-353879582035097859632790550598815176000000000000)
      constant := (9334304113896284731788421456140636905193807051454) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree097.table
  base := (535335144660753045826912927459288537133/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5503806000000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (698363968696081174354795015251240000000000000)
      linear := (-70853088091872066656465167668725635200000000000)
      constant := (1870773449032666641175701882076993467560095704950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell121.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122348532548770793521/25000000000000000000)
  centralHi := (97878826039016634817/20000000000000000000)
  directionLo := (491936454472399268509/100000000000000000000)
  directionHi := (49193645447239926851/10000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree098.table
  base := (137586697567443102807108958807163182384523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-51075106464040464994911234396142368000000000000)
      constant := (1361477767682022414640018401211795758727645142467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree098.table
  base := (137586697507740422440976757664365700381321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (27519030)
      previous := (13759515)
      next := (13759515)
      square := (498831406211486553110567868036600000000000000)
      linear := (-51130797370635048820617358400548368000000000000)
      constant := (1364330404527940429613186973280885367425208343409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell121.Kernel098
