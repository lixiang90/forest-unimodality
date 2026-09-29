import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell232.Parameters
import ForestUnimodality.BinomialMassData.Q2_3.Batch000_049
import ForestUnimodality.BinomialMassData.Q2_3.Batch050_099
import ForestUnimodality.BinomialMassData.Q35_52.Batch000_049
import ForestUnimodality.BinomialMassData.Q35_52.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree000.table
  base := (55428020302621358494832293/10000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-2361043571635770416117239290000000000000)
      constant := (166284060907864075484496879000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree000.table
  base := (55428020302621358494832293/10000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (595)
      previous := (0)
      next := (289)
      square := (23490055688689517321421362920000000000000)
      linear := (-40924755241686687212698814360000000000000)
      constant := (2882257055736310641731279236000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree001.table
  base := (20993521563230465756207254761276715565417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-12503912796912584476372032390000000000000)
      constant := (384412402642088348853305169122980880177506) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree001.table
  base := (8371912694517360212887174061561968277449/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-943097792693993486889958437780000000000000)
      constant := (28793499391884612276509864730541952777777620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (29863125692764953999/100000000000000000000)
  directionHi := (14931562846382477/50000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree002.table
  base := (3938368609970442777896522914932346626397/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-17924694878917857704392346910000000000000)
      constant := (300234423647088659310379026395128957100584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree002.table
  base := (15654578035952582775371140706472688609467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-1354173767246060040014832288880000000000000)
      constant := (22434544225542113913884418593701074999999384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29863125692764953999/100000000000000000000)
  centralHi := (14931562846382477/50000000000000000)
  directionLo := (21116418684780313781/50000000000000000000)
  directionHi := (42232837369560627563/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree003.table
  base := (5828567132155726409265990429277894545803/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-7781825653641043644137553810000000000000)
      constant := (80085674811145530971446678251334734549636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree003.table
  base := (5770928329603112640067747690433586717051/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-1765249741798126593139706139980000000000000)
      constant := (17923950912801678312637449623194918482905904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21116418684780313781/50000000000000000000)
  centralHi := (42232837369560627563/100000000000000000000)
  directionLo := (12931112743171106689/25000000000000000000)
  directionHi := (51724450972684426757/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree004.table
  base := (16892035488910556421754325531363963766527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-28766259042928404160432975950000000000000)
      constant := (199827505743975961674168521542275673898743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree004.table
  base := (16652760426775113182862189220733317917477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-2176325716350193146264579991080000000000000)
      constant := (14903118498777830465500926844815722912214452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12931112743171106689/25000000000000000000)
  centralHi := (51724450972684426757/100000000000000000000)
  directionLo := (59726251385529907999/100000000000000000000)
  directionHi := (14931562846382477/25000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree005.table
  base := (5922940600654063246724288576433176291073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-34187041124933677388453290470000000000000)
      constant := (175396550544841452835712208275797173239314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree005.table
  base := (2322541746477322042856833205874144616693/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-2587401690902259699389453842180000000000000)
      constant := (13099221046196547166414213784417108804422340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59726251385529907999/100000000000000000000)
  centralHi := (14931562846382477/25000000000000000)
  directionLo := (267103916278571747/400000000000000000)
  directionHi := (66775979069642936751/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree006.table
  base := (1970980095270170044925241423510034994279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-13202607735646316872157868330000000000000)
      constant := (54779063757806215115653112322120419931348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree006.table
  base := (7665451972890716239832426958565498366059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-2998477665454326252514327693280000000000000)
      constant := (12310738721705020035037072343140276895455884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267103916278571747/400000000000000000)
  centralHi := (66775979069642936751/100000000000000000000)
  directionLo := (2925976802874901777/4000000000000000000)
  directionHi := (36574710035936272213/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree007.table
  base := (2377451702512288763075422835158660349479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-45028605288944223844493919510000000000000)
      constant := (164388181320874779618664098252855886290622) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree007.table
  base := (4555607142866532021345768832266207377703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-3409553640006392805639201544380000000000000)
      constant := (12365032613638721186372529173974456187327228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2925976802874901777/4000000000000000000)
  centralHi := (36574710035936272213/50000000000000000000)
  directionLo := (79010403954119537181/100000000000000000000)
  directionHi := (39505201977059768591/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree008.table
  base := (142267224713278349964935380773002269423/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-50449387370949497072514234030000000000000)
      constant := (173906528587663571250593233231312326796912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree008.table
  base := (131120660360943684638612638497700255337/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-3820629614558459358764075395480000000000000)
      constant := (13136877996657314603706665019191125961724992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79010403954119537181/100000000000000000000)
  centralHi := (39505201977059768591/50000000000000000000)
  directionLo := (21116418684780313781/25000000000000000000)
  directionHi := (675725397912970041/800000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree009.table
  base := (38314755511567225019423192879790452603/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-18623389817651590100178182850000000000000)
      constant := (63872854300139694949352423049114970862472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree009.table
  base := (74603031318544145956808847538381016907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-4231705589110525911888949246580000000000000)
      constant := (14529460733770774054381881114534391134858264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21116418684780313781/25000000000000000000)
  centralHi := (675725397912970041/800000000000000000)
  directionLo := (44794688539147430999/50000000000000000000)
  directionHi := (89589377078294861999/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree010.table
  base := (-632115940664580454711277316153097104677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-61290951534960043528554863070000000000000)
      constant := (216535520567595401071552278109244252115814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree010.table
  base := (-280290406892014499538959824549853985393/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-4642781563662592465013823097680000000000000)
      constant := (16467822113470200506679639730771493529371660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44794688539147430999/50000000000000000000)
  centralHi := (89589377078294861999/100000000000000000000)
  directionLo := (94435495241030970819/100000000000000000000)
  directionHi := (4721774762051548541/5000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree011.table
  base := (-1260697080569399021694673246725692657101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-66711733616965316756575177590000000000000)
      constant := (247888621766617120294227831578937532172182) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree011.table
  base := (-1320017136294205614849698794909028625539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-5053857538214659018138696948780000000000000)
      constant := (18893832525934903157597783105745493298271272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94435495241030970819/100000000000000000000)
  centralHi := (4721774762051548541/5000000000000000000)
  directionLo := (99044782990123520443/100000000000000000000)
  directionHi := (24761195747530880111/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree012.table
  base := (-1765744430385709799590799367496333384793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-24044171899656863328198497370000000000000)
      constant := (95026395302856276179718150435021999691242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree012.table
  base := (-726666582529128522022161062614826120307/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-5464933512766725571263570799880000000000000)
      constant := (21762340402798026865873126977161887713362340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99044782990123520443/100000000000000000000)
  centralHi := (24761195747530880111/25000000000000000000)
  directionLo := (103448901945368853513/100000000000000000000)
  directionHi := (51724450972684426757/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree013.table
  base := (-2173199225169128804509734775721923965157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-77553297780975863212615806630000000000000)
      constant := (327640270762449437516350713537005368627174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree013.table
  base := (-4433310621266977943939787838574922521889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (595)
      previous := (0)
      next := (289)
      square := (23490055688689517321421362920000000000000)
      linear := (-452000729793753240337572665460000000000000)
      constant := (1926016844724166829947568756606604028861772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103448901945368853513/100000000000000000000)
  centralHi := (51724450972684426757/50000000000000000000)
  directionLo := (26918257732722527187/25000000000000000000)
  directionHi := (107673030930890108749/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree014.table
  base := (-2503325038162617985717171241070869556691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-82974079862981136440636121150000000000000)
      constant := (375207132009885632139034166420724347979562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree014.table
  base := (-5080455552431965341504980748673200385679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-6287085461870858677513318502080000000000000)
      constant := (28694098269693154405358186028246916539280996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26918257732722527187/25000000000000000000)
  centralHi := (107673030930890108749/100000000000000000000)
  directionLo := (11173758484049266577/10000000000000000000)
  directionHi := (111737584840492665771/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree015.table
  base := (-2771973615759864458934710554603633859347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-29464953981662136556218811890000000000000)
      constant := (142498146071930348108071992572378196843918) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree015.table
  base := (-44850898471680705767976335828039333121/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-6698161436422925230638192353180000000000000)
      constant := (32708620316129012923295618790093176351275500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11173758484049266577/10000000000000000000)
  centralHi := (111737584840492665771/100000000000000000000)
  directionLo := (23131877694755499209/20000000000000000000)
  directionHi := (57829694236888748023/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree016.table
  base := (-5983125807430902400833586666586584125027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-93815644026991682896676750190000000000000)
      constant := (484278666356583180499316216320720742874757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree016.table
  base := (-3017860440116140735251994148028717602489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-7109237410974991783763066204280000000000000)
      constant := (37065094687900232358783192786265173801434872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23131877694755499209/20000000000000000000)
  centralHi := (57829694236888748023/50000000000000000000)
  directionLo := (59726251385529907999/50000000000000000000)
  directionHi := (119452502771059815999/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree017.table
  base := (-6343668021047643349287820785028691648113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-99236426108996956124697064710000000000000)
      constant := (545384476479362058303686047554741775166983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree017.table
  base := (-1277570414802727899184843323900738611701/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-7520313385527058336887940055380000000000000)
      constant := (41750460518957608893433591700078003492450620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59726251385529907999/50000000000000000000)
  centralHi := (119452502771059815999/100000000000000000000)
  directionLo := (123128821542366478273/100000000000000000000)
  directionHi := (61564410771183239137/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree018.table
  base := (-830109521007833884209754861648245981929/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-34885736063667409784239126410000000000000)
      constant := (203558049307631067981104077520442096433704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree018.table
  base := (-3338947468828928923284384441322149751127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-7931389360079124890012813906480000000000000)
      constant := (46754483813290044335912551184282453536476296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123128821542366478273/100000000000000000000)
  centralHi := (61564410771183239137/50000000000000000000)
  directionLo := (63349256054340941343/50000000000000000000)
  directionHi := (126698512108681882687/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree019.table
  base := (-6886784182573728333491695269208105840359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-110077990273007502580737693750000000000000)
      constant := (680039375280296932582807682837127047436769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree019.table
  base := (-3458863319423573375538390643452229493513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-8342465334631191443137687757580000000000000)
      constant := (52069135605544364571660015166715085724770424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63349256054340941343/50000000000000000000)
  centralHi := (126698512108681882687/100000000000000000000)
  directionLo := (26034069406603100597/20000000000000000000)
  directionHi := (65085173516507751493/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree020.table
  base := (-7090866747236415503185724145700761364831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-115498772355012775808758008270000000000000)
      constant := (753394886407672840852059990288693147716521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree020.table
  base := (-56933410345713381071835352843531278313/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-8753541309183257996262561608680000000000000)
      constant := (57688109413552887097692915922721606982551500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26034069406603100597/20000000000000000000)
  centralHi := (65085173516507751493/50000000000000000000)
  directionLo := (267103916278571747/200000000000000000)
  directionHi := (133551958139285873501/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree021.table
  base := (-1452118361385461319342386303008460841107/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-40306518145672683012259440930000000000000)
      constant := (276891156600377254208500966994873087383395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree021.table
  base := (-1456415961310898166202457156784808355199/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-9164617283735324549387435459780000000000000)
      constant := (63606446164997816507053985523029847759427380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267103916278571747/200000000000000000)
  centralHi := (133551958139285873501/100000000000000000000)
  directionLo := (8553127123442247507/6250000000000000000)
  directionHi := (136850033975075960113/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree022.table
  base := (-3700925870624823586169510029406131496057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-126340336519023322264798637310000000000000)
      constant := (911822094044244487878718090790689633070974) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree022.table
  base := (-3709855914021095776907073316684733228049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-9575693258287391102512309310880000000000000)
      constant := (69820242197037467816675418617392240675677752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8553127123442247507/6250000000000000000)
  centralHi := (136850033975075960113/100000000000000000000)
  directionLo := (140070475386932712809/100000000000000000000)
  directionHi := (14007047538693271281/10000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree023.table
  base := (-3759650176083571887984665129438438817933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-131761118601028595492818951830000000000000)
      constant := (996798874919337657698584495370108101277206) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree023.table
  base := (-7534122548551737173886934399286525925311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-9986769232839457655637183161980000000000000)
      constant := (76326421580640704463421908669844808474489764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140070475386932712809/100000000000000000000)
  centralHi := (14007047538693271281/10000000000000000000)
  directionLo := (71609259791006081199/50000000000000000000)
  directionHi := (143218519582012162399/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree024.table
  base := (-7616616622542753222144678040452374392797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-45727300227677956240279755450000000000000)
      constant := (361856900526881553584741923798642876821609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree024.table
  base := (-3814450346378389833697317447603801712483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-10397845207391524208762057013080000000000000)
      constant := (83122558337928137711406601270439660084722984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71609259791006081199/50000000000000000000)
  centralHi := (143218519582012162399/100000000000000000000)
  directionLo := (2925976802874901777/2000000000000000000)
  directionHi := (146298840143745088851/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree025.table
  base := (-1539342289139683682243266168860887096727/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-142602682765039141948859580870000000000000)
      constant := (1178111375988268010942480511901260080647285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree025.table
  base := (-1926719792163410478885081531821149712403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-10808921181943590761886930864180000000000000)
      constant := (90206737423094253292936215687018111177662288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2925976802874901777/2000000000000000000)
  centralHi := (146298840143745088851/100000000000000000000)
  directionLo := (149315628463824769997/100000000000000000000)
  directionHi := (74657814231912384999/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree026.table
  base := (-7761889871906266889117874798062981667893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-148023464847044415176879895390000000000000)
      constant := (1274400152689758560349946441737433164988963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree026.table
  base := (-7770296093928771399803951462113104406751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (595)
      previous := (0)
      next := (289)
      square := (23490055688689517321421362920000000000000)
      linear := (-863076704345819793462446516560000000000000)
      constant := (7505957374506385593117716169520118570848948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149315628463824769997/100000000000000000000)
  centralHi := (74657814231912384999/50000000000000000000)
  directionLo := (76136330322141275627/50000000000000000000)
  directionHi := (30454532128856510251/20000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree027.table
  base := (-1562795720937498767152333830422738865723/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-51148082309683229468300069970000000000000)
      constant := (458140197117808517452470775883658917014155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree027.table
  base := (-7820921043325482701318390198118563870799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-11631073131047723868136678566380000000000000)
      constant := (105233487441867935307343058414934350823339876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76136330322141275627/50000000000000000000)
  centralHi := (30454532128856510251/20000000000000000000)
  directionLo := (155173352918053280269/100000000000000000000)
  directionHi := (15517335291805328027/10000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree028.table
  base := (-4909016443954223636368375283036665277/6250000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-158865029011054961632920524430000000000000)
      constant := (1478159653982707059861502990724272020011200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree028.table
  base := (-7860154149049609911362580233928343949927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-12042149105599790421261552417480000000000000)
      constant := (113173915653577877237669898301064439489849348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155173352918053280269/100000000000000000000)
  centralHi := (15517335291805328027/10000000000000000000)
  directionLo := (158020807908239074363/100000000000000000000)
  directionHi := (39505201977059768591/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree029.table
  base := (-1971095656958282184397819742808414362241/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-164285811093060234860940838950000000000000)
      constant := (1585606993826521453751506538518897082959324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree029.table
  base := (-315564159247165451862261148607265212563/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-12453225080151856974386426268580000000000000)
      constant := (121397981110340121813275705031699717907685300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158020807908239074363/100000000000000000000)
  centralHi := (39505201977059768591/25000000000000000000)
  directionLo := (20102231688964004449/12500000000000000000)
  directionHi := (160817853511712035593/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree030.table
  base := (-1580952093842315128304343633885567660619/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-56568864391688502696320384490000000000000)
      constant := (565584798225608004199811083291716485090715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree030.table
  base := (-3954324409194861314436838514322984022069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-12864301054703923527511300119680000000000000)
      constant := (129905090095769922352306432229385325602162712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20102231688964004449/12500000000000000000)
  centralHi := (160817853511712035593/100000000000000000000)
  directionLo := (32713415159078912293/20000000000000000000)
  directionHi := (81783537897697280733/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree031.table
  base := (-1583257038795826235633065189033993544519/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-175127375257070781316981467990000000000000)
      constant := (1811595328297961442571621653713470290496645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree031.table
  base := (-7919484900773529313913388529511687264839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-13275377029255990080636173970780000000000000)
      constant := (138694771951564978420576910266012599408968836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32713415159078912293/20000000000000000000)
  centralHi := (81783537897697280733/50000000000000000000)
  directionLo := (166270846994890321109/100000000000000000000)
  directionHi := (16627084699489032111/10000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree032.table
  base := (-7919533460561595178338542591637483451963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-180548157339076054545001782510000000000000)
      constant := (1930124604764101545190723787395262648932333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree032.table
  base := (-7922164467236797875026192143031871337361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-13686453003808056633761047821880000000000000)
      constant := (147766653364224670748302181588110454975943964) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (166270846994890321109/100000000000000000000)
  centralHi := (16627084699489032111/10000000000000000000)
  directionLo := (21116418684780313781/12500000000000000000)
  directionHi := (168931349478242510249/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree033.table
  base := (-316598557974591986837826428131790671907/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-61989646473693775924340699010000000000000)
      constant := (684112698650530610732200339190115699606975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree033.table
  base := (-1583425153455704860866403222344019962509/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-14097528978360123186885921672980000000000000)
      constant := (157120438077087678044809174703739712526719580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21116418684780313781/12500000000000000000)
  centralHi := (168931349478242510249/100000000000000000000)
  directionLo := (171550596363527644699/100000000000000000000)
  directionHi := (1715505963635276447/1000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree034.table
  base := (-7902941678654025442057533000287414832767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-191389721503086601001042411550000000000000)
      constant := (2178232516696044776514615669757413266505097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree034.table
  base := (-3952358380289646250627842722385390280627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-14508604952912189740010795524080000000000000)
      constant := (166755890869409925594086707906684952340592296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171550596363527644699/100000000000000000000)
  centralHi := (1715505963635276447/1000000000000000000)
  directionLo := (17413044934423118483/10000000000000000000)
  directionHi := (174130449344231184831/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree035.table
  base := (-3941878632348844667608483980801453935781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-196810503585091874229062726070000000000000)
      constant := (2307805251451044626552882467645573829155942) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree035.table
  base := (-7885213846852134810611889255567741488417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-14919680927464256293135669375180000000000000)
      constant := (176672824894985403531040051356298706753830108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17413044934423118483/10000000000000000000)
  centralHi := (174130449344231184831/100000000000000000000)
  directionLo := (176672634171129460127/100000000000000000000)
  directionHi := (5521019817847795629/3125000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree036.table
  base := (-3928821094337135898907030464949498616693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-67410428555699049152361013530000000000000)
      constant := (813684738961995019428296851050303008299842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree036.table
  base := (-982354584883340224162315995749762645647/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-15330756902016322846260543226280000000000000)
      constant := (186871091668406614556502224367385283612341024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176672634171129460127/100000000000000000000)
  centralHi := (5521019817847795629/3125000000000000000)
  directionLo := (179178754156589723997/100000000000000000000)
  directionHi := (89589377078294861999/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree037.table
  base := (-3912390453325920666547783889122943873429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-207652067749102420685103355110000000000000)
      constant := (2577977752896253455181419123415787010278278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree037.table
  base := (-1565151977431831545134660413973479639571/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-15741832876568389399385417077380000000000000)
      constant := (197350573139836752179655421406132138818250020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179178754156589723997/100000000000000000000)
  centralHi := (89589377078294861999/50000000000000000000)
  directionLo := (90825151000768363171/50000000000000000000)
  directionHi := (181650302001536726343/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree038.table
  base := (-1557064092329474868098734589313937154113/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-213072849831107693913123669630000000000000)
      constant := (2718574536094697029647578518480872828064915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree038.table
  base := (-7786122362568620836557687557825399247033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-16152908851120455952510290928480000000000000)
      constant := (208111175418662931917816324702860030109005692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90825151000768363171/50000000000000000000)
  centralHi := (181650302001536726343/100000000000000000000)
  directionLo := (23011083774112862257/12500000000000000000)
  directionHi := (184088670192902898057/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree039.table
  base := (-120927783087624012733433346598210872407/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-72831210637704322380381328050000000000000)
      constant := (954281170368597395909662172873143512497856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree039.table
  base := (-3870017307745767888566756519937218069451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (595)
      previous := (0)
      next := (289)
      square := (23490055688689517321421362920000000000000)
      linear := (-1274152678897886346587320367660000000000000)
      constant := (16857909523076336208214309085939029320777096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23011083774112862257/12500000000000000000)
  centralHi := (184088670192902898057/100000000000000000000)
  directionLo := (46623790044309229127/25000000000000000000)
  directionHi := (186495160177236916509/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree040.table
  base := (-7687047425786719317035924647321761439189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-223914413995118240369164298670000000000000)
      constant := (3010783835968260214380223565374104147047299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree040.table
  base := (-7687584608169210485744308532647996479031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-16975060800224589058760038630680000000000000)
      constant := (230475458821349944380244275357929954380175044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46623790044309229127/25000000000000000000)
  centralHi := (186495160177236916509/100000000000000000000)
  directionLo := (94435495241030970819/50000000000000000000)
  directionHi := (188870990482061941639/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree041.table
  base := (-7628403047931355364802902795693890861/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-229335196077123513597184613190000000000000)
      constant := (3162394838726372407939103732658754982251000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree041.table
  base := (-7628842382276667799601612789404291474221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-17386136774776655611884912481780000000000000)
      constant := (242079033134563337500236096227825198963426604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94435495241030970819/50000000000000000000)
  centralHi := (188870990482061941639/100000000000000000000)
  directionLo := (191217303928846907229/100000000000000000000)
  directionHi := (19121730392884690723/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree042.table
  base := (-756350459291339096858159476967540295111/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-78251992719709595608401642570000000000000)
      constant := (1105891994300094951437519561730973791146670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree042.table
  base := (-7563863731471012719560016086469508488887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-17797212749328722165009786332880000000000000)
      constant := (253963509023120347086183777700096612261512388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191217303928846907229/100000000000000000000)
  centralHi := (19121730392884690723/10000000000000000000)
  directionLo := (1548281392470170103/800000000000000000)
  directionHi := (48383793514692815719/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree043.table
  base := (-7492399669971322185938283402409761808123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-240176760241134060053225242230000000000000)
      constant := (3476626840006851088982491877478312143726893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree043.table
  base := (-3746346558714159892808424705329433377387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-18208288723880788718134660183980000000000000)
      constant := (266128856430927946749049124027657106073772776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1548281392470170103/800000000000000000)
  centralHi := (48383793514692815719/25000000000000000000)
  directionLo := (97912805436904890437/50000000000000000000)
  directionHi := (1566604886990478247/800000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree044.table
  base := (-1483025263908482709581686640119942567363/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-245597542323139333281245556750000000000000)
      constant := (3639247067682135731169584128954602584468665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree044.table
  base := (-926920748270445674468018169814394918501/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-18619364698432855271259534035080000000000000)
      constant := (278575051396480012443803041175243752280746592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97912805436904890437/50000000000000000000)
  centralHi := (1566604886990478247/800000000000000000)
  directionLo := (99044782990123520443/50000000000000000000)
  directionHi := (198089565980247040887/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree045.table
  base := (-7331714949317298903480685765485045420549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-83672774801714868836421957090000000000000)
      constant := (1268512130752307692077645888403544863738353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree045.table
  base := (-183297765217016824421186117249238365603/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-19030440672984921824384407886180000000000000)
      constant := (291302074808577891933857383589143094594094880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99044782990123520443/50000000000000000000)
  centralHi := (198089565980247040887/100000000000000000000)
  directionLo := (801311748835715241/400000000000000000)
  directionHi := (200327937208928810251/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree046.table
  base := (-3621094938391954310476677258394001331871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-256439106487149879737286185790000000000000)
      constant := (3975494594873821750857867665468907976026322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree046.table
  base := (-90529369301965882743117164463715839517/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-19441516647536988377509281737280000000000000)
      constant := (304309911417217508630018856260952247398920640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (801311748835715241/400000000000000000)
  centralHi := (200327937208928810251/100000000000000000000)
  directionLo := (40508314555175658373/20000000000000000000)
  directionHi := (101270786387939145933/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree047.table
  base := (-3573285279328687366674194636536209054587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-261859888569155152965306500310000000000000)
      constant := (4149121500422395566747176581362348237017434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree047.table
  base := (-3573350401729140731117140131681600454879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-19852592622089054930634155588380000000000000)
      constant := (317598549047054174490536838926328976185003592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40508314555175658373/20000000000000000000)
  centralHi := (101270786387939145933/50000000000000000000)
  directionLo := (204731275037958674717/100000000000000000000)
  directionHi := (102365637518979337359/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree048.table
  base := (-7044872571060998177093578303997558204473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-89093556883720142064442271610000000000000)
      constant := (1442138989572511605157671439488007325386581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree048.table
  base := (-1761244693659899524059119643212797423433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-20263668596641121483759029439480000000000000)
      constant := (331167977971762106123872136291952595767037168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204731275037958674717/100000000000000000000)
  centralHi := (102365637518979337359/50000000000000000000)
  directionLo := (103448901945368853513/50000000000000000000)
  directionHi := (206897803890737707027/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree049.table
  base := (-6937108391218649715931127078608726670391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-272701452733165699421347129350000000000000)
      constant := (4507380887464224660161701027552521459966481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree049.table
  base := (-6937194959342035635976931495709441812721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-20674744571193188036883903290580000000000000)
      constant := (345018190416232112512608577092562917334600604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103448901945368853513/50000000000000000000)
  centralHi := (206897803890737707027/100000000000000000000)
  directionLo := (52260469962338669499/25000000000000000000)
  directionHi := (209041879849354677997/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree050.table
  base := (-3411644010511809863612899157456397474283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-278122234815170972649367443870000000000000)
      constant := (4692013166645425487416953844165784845462906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree050.table
  base := (-3411679279437467213352133869642184303439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-21085820545745254590008777141680000000000000)
      constant := (359149180160379079583358088321993766821750472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52260469962338669499/25000000000000000000)
  centralHi := (209041879849354677997/100000000000000000000)
  directionLo := (211164186847803137811/100000000000000000000)
  directionHi := (52791046711950784453/25000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree051.table
  base := (-268136779383899874943876272565332192337/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-94514338965725415292462586130000000000000)
      constant := (1626771244681347666425066311697600085574725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree051.table
  base := (-3351738470394284165304382245973535684879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-21496896520297321143133650992780000000000000)
      constant := (373560942223739022205280042600906279754043592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211164186847803137811/100000000000000000000)
  centralHi := (52791046711950784453/25000000000000000000)
  directionLo := (213265374787460034137/100000000000000000000)
  directionHi := (106632687393730017069/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree052.table
  base := (-1644377306349768709193565574960933851477/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-288963798979181519105408072910000000000000)
      constant := (5072282531668948052600868012821406381346828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree052.table
  base := (-822194501299291201321991844752467179521/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (595)
      previous := (0)
      next := (289)
      square := (23490055688689517321421362920000000000000)
      linear := (-1685228653449952899712194218760000000000000)
      constant := (29865651739563187631435679472182973653319264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213265374787460034137/100000000000000000000)
  centralHi := (106632687393730017069/50000000000000000000)
  directionLo := (215346061861780217497/100000000000000000000)
  directionHi := (107673030930890108749/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree053.table
  base := (-6445562423235312712205413099109048715209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-294384581061186792333428387430000000000000)
      constant := (5267919512901878015534933142408018561563119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree053.table
  base := (-3222800253332154396371849371798253179363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-22319048469401454249383398694980000000000000)
      constant := (403226768128581197397840225875091261701501224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215346061861780217497/100000000000000000000)
  centralHi := (107673030930890108749/50000000000000000000)
  directionLo := (217406836680725269753/100000000000000000000)
  directionHi := (108703418340362634877/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree054.table
  base := (-63075832473855892332529788010399669037/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-99935121047730688520482900650000000000000)
      constant := (1822408213406439493159043582516880099288900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree054.table
  base := (-1261522847590701147524766716097758718493/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-22730124443953520802508272546080000000000000)
      constant := (418480826192070316867103259469939575531493660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217406836680725269753/100000000000000000000)
  centralHi := (108703418340362634877/50000000000000000000)
  directionLo := (8777930408624705331/4000000000000000000)
  directionHi := (54862065053904408319/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree055.table
  base := (-3081787529378318160118480594830205832161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-305226145225197338789469016470000000000000)
      constant := (5670197883373108857144580812193056295021102) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree055.table
  base := (-3081800134911146755300783066369133567957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-23141200418505587355633146397180000000000000)
      constant := (434015644732469985424252520562831431416122136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8777930408624705331/4000000000000000000)
  centralHi := (54862065053904408319/25000000000000000000)
  directionLo := (221470867582631073359/100000000000000000000)
  directionHi := (2768385844782888417/1250000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree056.table
  base := (-6013540571364225015635364370483417805109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-310646927307202612017489330990000000000000)
      constant := (5876839217937107209154981299385649239754019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree056.table
  base := (-6013561074723087662942799912109629822671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-23552276393057653908758020248280000000000000)
      constant := (449831222078402370156632258379813890239874404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221470867582631073359/100000000000000000000)
  centralHi := (2768385844782888417/1250000000000000000)
  directionLo := (223475169680985331541/100000000000000000000)
  directionHi := (111737584840492665771/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree057.table
  base := (-234299279254029153591008320812295555563/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-105355903129735961748503215170000000000000)
      constant := (2029049541382010724608463010679077833332775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree057.table
  base := (-5857498651318381856317553323839718274371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-23963352367609720461882894099380000000000000)
      constant := (465927556878771625348953540478946850446525204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223475169680985331541/100000000000000000000)
  centralHi := (111737584840492665771/50000000000000000000)
  directionLo := (112730827350027756153/50000000000000000000)
  directionHi := (225461654700055512307/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree058.table
  base := (-2847700535042770709186825827519236006681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-321488491471213158473529960030000000000000)
      constant := (6301126085967559208524349574504653751879742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree058.table
  base := (-1139082923922104572000219261143111444631/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-24374428342161787015007767950480000000000000)
      constant := (482304648038456164585186284382286283317147220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112730827350027756153/50000000000000000000)
  centralHi := (225461654700055512307/100000000000000000000)
  directionLo := (113715394753996415739/50000000000000000000)
  directionHi := (227430789507992831479/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree059.table
  base := (-1381824821642760594772467492723237477827/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-326909273553218431701550274550000000000000)
      constant := (6518771590360666896602930354521963450798228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree059.table
  base := (-1381827574200548505293953089736674608261/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-24785504316713853568132641801580000000000000)
      constant := (498962494667026973922635198843014531859262256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113715394753996415739/50000000000000000000)
  centralHi := (227430789507992831479/100000000000000000000)
  directionLo := (45876604186609462043/20000000000000000000)
  directionHi := (28672877616630913777/12500000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree060.table
  base := (-669147226665170800251842734230377434219/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-110776685211741234976523529690000000000000)
      constant := (2246695042227576008646771153978470941578744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree060.table
  base := (-41821771545339965211622424291000334309/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-25196580291265920121257515652680000000000000)
      constant := (515901096037844812101202008934948323072910848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45876604186609462043/20000000000000000000)
  centralHi := (28672877616630913777/12500000000000000000)
  directionLo := (231318776947554992091/100000000000000000000)
  directionHi := (57829694236888748023/25000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree061.table
  base := (-646629702379975440747858033885210110007/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-337750837717228978157590903590000000000000)
      constant := (6965066686215412986186987524580264872079496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree061.table
  base := (-5173044883503808488122411314176856735551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-25607656265817986674382389503780000000000000)
      constant := (533120451555428498090825953635578944846767524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231318776947554992091/100000000000000000000)
  centralHi := (57829694236888748023/25000000000000000000)
  directionLo := (116619233881738582979/50000000000000000000)
  directionHi := (233238467763477165959/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree062.table
  base := (-1246719875187415569091147933907514465937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-343171619799234251385611218110000000000000)
      constant := (7193716261785512000614619351299329479226268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree062.table
  base := (-623360674911407169733676399467370676673/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-26018732240370053227507263354880000000000000)
      constant := (550620560729415619160320614889230459380552416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116619233881738582979/50000000000000000000)
  centralHi := (233238467763477165959/100000000000000000000)
  directionLo := (235142486847435666589/100000000000000000000)
  directionHi := (23514248684743566659/10000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree063.table
  base := (-4794704117498202864147773896508399589261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-116197467293746508204543844210000000000000)
      constant := (2475344615820533242441439431810474801232217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree063.table
  base := (-191788356231939895670014142114777439159/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-26429808214922119780632137205980000000000000)
      constant := (568401423153778513890540934583022761278212900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235142486847435666589/100000000000000000000)
  centralHi := (23514248684743566659/10000000000000000000)
  directionLo := (47406242372471722309/20000000000000000000)
  directionHi := (118515605931179305773/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree064.table
  base := (-459651201732622151686508726716502707939/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-354013183963244797841651847150000000000000)
      constant := (7662019438311309000268290268355514756285490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree064.table
  base := (-1149128975862498566876533276125052395901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-26840884189474186333757011057080000000000000)
      constant := (586463038490230243483334067886957858321483696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47406242372471722309/20000000000000000000)
  centralHi := (118515605931179305773/50000000000000000000)
  directionLo := (59726251385529907999/25000000000000000000)
  directionHi := (238905005542119631997/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree065.table
  base := (-4392303658855091418556346902635557823753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-359433966045250071069672161670000000000000)
      constant := (7901673030207047460790176934576279979586223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree065.table
  base := (-4392306812066888736991170070482411110061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (595)
      previous := (0)
      next := (289)
      square := (23490055688689517321421362920000000000000)
      linear := (-2096304628002019452837068069860000000000000)
      constant := (46523492804228593599265109748647414622276828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59726251385529907999/25000000000000000000)
  centralHi := (238905005542119631997/100000000000000000000)
  directionLo := (6019105412622693593/2500000000000000000)
  directionHi := (240764216504907743721/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree066.table
  base := (-836415885714212946791566132943752558779/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-121618249375751781432564158730000000000000)
      constant := (2714998206556812946469117264445843711618315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree066.table
  base := (-2091040993264995701316487862039390798429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-27663036138578319440006758759280000000000000)
      constant := (623428526808103505844637013498672743640523992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6019105412622693593/2500000000000000000)
  centralHi := (240764216504907743721/100000000000000000000)
  directionLo := (242609180010493355417/100000000000000000000)
  directionHi := (121304590005246677709/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree067.table
  base := (-991459913667373277690494477445593582803/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-370275530209260617525712790710000000000000)
      constant := (8391984203747724971290582890431958631019092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree067.table
  base := (-1982920864649258637537534970558154014183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-28074112113130385993131632610380000000000000)
      constant := (642332399345163181298710808749667875772824584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242609180010493355417/100000000000000000000)
  centralHi := (121304590005246677709/50000000000000000000)
  directionLo := (48888043733209798797/20000000000000000000)
  directionHi := (122220109333024496993/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree068.table
  base := (-29246754829283113331344164087838507981/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-375696312291265890753733105230000000000000)
      constant := (8642641779909925098822880846570810038805888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree068.table
  base := (-1871793150210179168769790779759335774673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-28485188087682452546256506461480000000000000)
      constant := (661517023890358368172009653390965378032642104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48888043733209798797/20000000000000000000)
  centralHi := (122220109333024496993/50000000000000000000)
  directionLo := (123128821542366478273/50000000000000000000)
  directionHi := (246257643084732956547/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree069.table
  base := (-351531456170108065406051016474053449983/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-127039031457757054660584473250000000000000)
      constant := (2965655781990931734801957857925778396500510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree069.table
  base := (-439414490692598115137946929232302189077/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-28896264062234519099381380312580000000000000)
      constant := (680982400291152863720725451580874209761471584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123128821542366478273/50000000000000000000)
  centralHi := (246257643084732956547/100000000000000000000)
  directionLo := (15503859531302702023/6250000000000000000)
  directionHi := (248061752500843232369/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree070.table
  base := (-410128712106416565087536683159457266003/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-386537876455276437209773734270000000000000)
      constant := (9154960900032625471336624575412519076847784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree070.table
  base := (-1640515401156872396765586482209733436069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-29307340036786585652506254163680000000000000)
      constant := (700728528413932599253849657252802440394434712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15503859531302702023/6250000000000000000)
  centralHi := (248061752500843232369/100000000000000000000)
  directionLo := (124926417672495798219/50000000000000000000)
  directionHi := (249852835344991596439/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree071.table
  base := (-3040730209677528606472115978173144862469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-391958658537281710437794048790000000000000)
      constant := (9416622440414709089113867433816441696237779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree071.table
  base := (-760182776384515577356534401019928843313/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-29718416011338652205631128014780000000000000)
      constant := (720755408140533569507670126312604612407681648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124926417672495798219/50000000000000000000)
  centralHi := (249852835344991596439/100000000000000000000)
  directionLo := (251631169782428504839/100000000000000000000)
  directionHi := (6290779244560712621/2500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree072.table
  base := (-111776650616498719971776554852888275409/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-132459813539762327888604787770000000000000)
      constant := (3227317321877316955315445407826033379344325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree072.table
  base := (-2794416991275586371922289146344002370789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-30129491985890718758756001865880000000000000)
      constant := (741063039365457964623668396579871454397346636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251631169782428504839/100000000000000000000)
  centralHi := (6290779244560712621/2500000000000000000)
  directionLo := (253397024217363765373/100000000000000000000)
  directionHi := (126698512108681882687/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree073.table
  base := (-2542088012140496218137009152784140709767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-402800222701292256893834677830000000000000)
      constant := (9950949474351591692163302546324942733612097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree073.table
  base := (-254208860015631797425745498439665930603/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-30540567960442785311880875716980000000000000)
      constant := (761651421993639903930415696736810358309123720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253397024217363765373/100000000000000000000)
  centralHi := (126698512108681882687/50000000000000000000)
  directionLo := (127575328882935979777/50000000000000000000)
  directionHi := (51030131553174391911/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree074.table
  base := (-1141872791886420567458571778012528681399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-408221004783297530121854992350000000000000)
      constant := (10223614965368430516917511226755774483734818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree074.table
  base := (-570936515008519124406758876509937201157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-30951643934994851865005749568080000000000000)
      constant := (782520555938650205526223936121267129808071472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127575328882935979777/50000000000000000000)
  centralHi := (51030131553174391911/20000000000000000000)
  directionLo := (64223080174935452881/25000000000000000000)
  directionHi := (10275692827989672461/4000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree075.table
  base := (-2019389102444798987018057931215551544709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-137880595621767601116625102290000000000000)
      constant := (3499982812527749891357504365706353345365873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree075.table
  base := (-100969474406159851582853493706820854919/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-31362719909546918418130623419180000000000000)
      constant := (803670441121251978890505912259146282041495120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64223080174935452881/25000000000000000000)
  centralHi := (10275692827989672461/4000000000000000000)
  directionLo := (258622254863422133783/100000000000000000000)
  directionHi := (32327781857927766723/12500000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree076.table
  base := (-437254670112444164089917427491756709957/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-419062568947308076577895621390000000000000)
      constant := (10779949889985408501691028900530296758441548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree076.table
  base := (-437254748180095700048600315657108469471/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-31773795884098984971255497270280000000000000)
      constant := (825101077468236652643941159164863178698550416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258622254863422133783/100000000000000000000)
  centralHi := (32327781857927766723/12500000000000000000)
  directionLo := (26034069406603100597/10000000000000000000)
  directionHi := (260340694066031005971/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree077.table
  base := (-1472634421802182703896764486498848859633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-424483351029313349805915935910000000000000)
      constant := (11063619321638777322724465566641510360263303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree077.table
  base := (-73631733729740412122444046966754735619/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-32184871858651051524380371121380000000000000)
      constant := (846812464911484264865623817381371975974431120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26034069406603100597/10000000000000000000)
  centralHi := (260340694066031005971/100000000000000000000)
  directionLo := (65511966112556791321/25000000000000000000)
  directionHi := (52409572890045433057/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree078.table
  base := (-148779552937845184524039860481403456773/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-143301377703772874344645416810000000000000)
      constant := (3783652243890116479351252101948446317037448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree078.table
  base := (-1190236628112796532357496201281868479319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (595)
      previous := (0)
      next := (289)
      square := (23490055688689517321421362920000000000000)
      linear := (-2507380602554086005961941920960000000000000)
      constant := (66831123337477167776151729499683342839075412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65511966112556791321/25000000000000000000)
  centralHi := (52409572890045433057/20000000000000000000)
  directionLo := (263743984839591191901/100000000000000000000)
  directionHi := (131871992419795595951/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree079.table
  base := (-901824776565254903330200156920632025693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-435324915193323896261956564950000000000000)
      constant := (11641962119261001170308146312847714311768763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree079.table
  base := (-450912471075008689662499518902343138327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-33007023807755184630630118823580000000000000)
      constant := (891077492835313448593429545163606532076981896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263743984839591191901/100000000000000000000)
  centralHi := (131871992419795595951/50000000000000000000)
  directionLo := (265429267066027190929/100000000000000000000)
  directionHi := (26542926706602719093/10000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree080.table
  base := (-303699783425757414533613481414944311907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-440745697275329169489976879470000000000000)
      constant := (11936635483637975852893824219734531002385674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree080.table
  base := (-607399700833479091650999750963606769809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-33418099782307251183754992674680000000000000)
      constant := (913631133198945209759584465820348601823609116) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265429267066027190929/100000000000000000000)
  centralHi := (26542926706602719093/10000000000000000000)
  directionLo := (267103916278571747/100000000000000000)
  directionHi := (267103916278571747001/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree081.table
  base := (-30696087575278319916373631744390029417/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-148722159785778147572665731330000000000000)
      constant := (4078325608022917436099648997787668299117490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree081.table
  base := (-153480492073537455400955789919695715233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-33829175756859317736879866525780000000000000)
      constant := (936465524424029352757205950116491071393004984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267103916278571747/100000000000000000)
  centralHi := (267103916278571747001/100000000000000000000)
  directionLo := (67192032808721146499/25000000000000000000)
  directionHi := (268768131234884585997/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree082.table
  base := (-20351229893417431614566299697372573/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-451587261439339715946017508510000000000000)
      constant := (12536986139856026057723978910302568091171075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree082.table
  base := (-508868427650545246017438134429028573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-34240251731411384290004740376880000000000000)
      constant := (959580666458962169887369438802371125976684652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67192032808721146499/25000000000000000000)
  centralHi := (268768131234884585997/100000000000000000000)
  directionLo := (135211052288296704283/50000000000000000000)
  directionHi := (270422104576593408567/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree083.table
  base := (311956644141333929160557159637158236859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-457008043521344989174037823030000000000000)
      constant := (12842663430333585650381888979336734424131731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree083.table
  base := (311956573226860742381599726436810491807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-34651327705963450843129614227980000000000000)
      constant := (982976559254329458264533615805333783892461532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135211052288296704283/50000000000000000000)
  centralHi := (270422104576593408567/100000000000000000000)
  directionLo := (26568947567341083/9765625000000000)
  directionHi := (272066023089572689921/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree084.table
  base := (630435327966416710763748144089979682809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-154142941867783420800686045850000000000000)
      constant := (4384002898287636604202783228352269939048427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree084.table
  base := (78804408827501873242694227470354046803/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-35062403680515517396254488079080000000000000)
      constant := (1006653202762678421767588256125759674685110624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26568947567341083/9765625000000000)
  centralHi := (272066023089572689921/100000000000000000000)
  directionLo := (8553127123442247507/3125000000000000000)
  directionHi := (10948002718006076809/4000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree085.table
  base := (954927202544270856772209594899700063093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-467849607685355535630078452070000000000000)
      constant := (13465021932830345765933138034654097300567837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree085.table
  base := (954927156176378401612061080166980099467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-35473479655067583949379361930180000000000000)
      constant := (1030610596938328067158669833940755378547239692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8553127123442247507/3125000000000000000)
  centralHi := (10948002718006076809/4000000000000000000)
  directionLo := (137662207479085973601/50000000000000000000)
  directionHi := (275324414958171947203/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree086.table
  base := (128543220219303803651715889964921837327/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-473270389767360808858098766590000000000000)
      constant := (13781703143644756785380234984616842965359430) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree086.table
  base := (642716082353490199912356085684742110263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-35884555629619650502504235781280000000000000)
      constant := (1054848741737210650319230104538995771333075576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137662207479085973601/50000000000000000000)
  centralHi := (275324414958171947203/100000000000000000000)
  directionLo := (55387846951547605713/20000000000000000000)
  directionHi := (138469617378869014283/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree087.table
  base := (1621950263513427268867136807013180883253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-159563723949788694028706360370000000000000)
      constant := (4700684108911849750706485800561039542649759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree087.table
  base := (1621950233211887054692292851380450992809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-36295631604171717055629109632380000000000000)
      constant := (1079367637116738215915369311092895684871138884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55387846951547605713/20000000000000000000)
  centralHi := (138469617378869014283/50000000000000000000)
  directionLo := (34818086630806780057/12500000000000000000)
  directionHi := (278544693046454240457/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree088.table
  base := (982240662601832685936382414969155248197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-484111953931371355314139395630000000000000)
      constant := (14426069481551007207513260879469444794467546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree088.table
  base := (982240650356420096367199092943314197139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-36706707578723783608753983483480000000000000)
      constant := (1104167283035689461421814699866859360794531928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34818086630806780057/12500000000000000000)
  centralHi := (278544693046454240457/100000000000000000000)
  directionLo := (280140950773865425619/100000000000000000000)
  directionHi := (14007047538693271281/5000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree089.table
  base := (1156512663951096946385140936116778503099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-489532736013376628542159710150000000000000)
      constant := (14753754607556876625486771568110102013055782) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree089.table
  base := (2313025308110310289071198131052955804703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-37117783553275850161878857334580000000000000)
      constant := (1129247679454113104879747505751254298123979228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280140950773865425619/100000000000000000000)
  centralHi := (14007047538693271281/5000000000000000000)
  directionLo := (140864082164889685837/50000000000000000000)
  directionHi := (11269126573191174867/4000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree090.table
  base := (333447776756619521607298258349580695119/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-164984506031793967256726674890000000000000)
      constant := (5028369234745050998703892583600389936682856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree090.table
  base := (1333791099030216028274234376249111967833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-37528859527827916715003731185680000000000000)
      constant := (1154608826333244693355051473366438799380510216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140864082164889685837/50000000000000000000)
  centralHi := (11269126573191174867/4000000000000000000)
  directionLo := (283306485723092912457/100000000000000000000)
  directionHi := (141653242861546456229/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree091.table
  base := (3028151927789130317991712473632532147843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-500374300177387174998200339190000000000000)
      constant := (15420128771083034922340671143082692789330587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree091.table
  base := (757037978717046749443865269907235484819/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (595)
      previous := (0)
      next := (289)
      square := (23490055688689517321421362920000000000000)
      linear := (-2918456577106152559086815772060000000000000)
      constant := (90788517202725722641806958185253204980842352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283306485723092912457/100000000000000000000)
  centralHi := (141653242861546456229/50000000000000000000)
  directionLo := (71219015687925180067/25000000000000000000)
  directionHi := (284876062751700720269/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree092.table
  base := (3394734414831974460057789030949835133083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-505795082259392448226220653710000000000000)
      constant := (15758817807612013727360739496398548516197747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree092.table
  base := (424341800549239093360776896598587286811/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-38351011476932049821253478887880000000000000)
      constant := (1206173371324083796085739065957605160047073888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71219015687925180067/25000000000000000000)
  centralHi := (284876062751700720269/100000000000000000000)
  directionLo := (71609259791006081199/25000000000000000000)
  directionHi := (286437039164024324797/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree093.table
  base := (235458101400131255927746418409447497143/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-170405288113799240484746989410000000000000)
      constant := (5367058271115691638211322917783653479862864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree093.table
  base := (941832403492697761324068885351508696479/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-38762087451484116374378352738980000000000000)
      constant := (1232376769363590129438994210102752979515279216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71609259791006081199/25000000000000000000)
  centralHi := (286437039164024324797/100000000000000000000)
  directionLo := (35998694351582626873/12500000000000000000)
  directionHi := (57597910962532202997/20000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree094.table
  base := (4145937499141009686201416399547132543/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-516636646423402994682261282750000000000000)
      constant := (16447199787825992006335020100355924192887000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree094.table
  base := (4145937492331423626446037829713111303369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-39173163426036182927503226590080000000000000)
      constant := (1258860917719296633175061596299236063241077444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35998694351582626873/12500000000000000000)
  centralHi := (57597910962532202997/20000000000000000000)
  directionLo := (18095859112538590477/6250000000000000000)
  directionHi := (289533745800617447633/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree095.table
  base := (4530557995041151903910262271515691344411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-522057428505408267910281597270000000000000)
      constant := (16796892730598697040491914006543641222099699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree095.table
  base := (4530557989541971229959967653917873382029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-39584239400588249480628100441180000000000000)
      constant := (1285625816357448031953927363303610982406251604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18095859112538590477/6250000000000000000)
  centralHi := (289533745800617447633/100000000000000000000)
  directionLo := (58213948924112145239/20000000000000000000)
  directionHi := (72767436155140181549/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree096.table
  base := (2460595530691541211851861952473134020031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (34)
      previous := (0)
      next := (17)
      square := (1355195520501318307005078630000000000000)
      linear := (-175826070195804513712767303930000000000000)
      constant := (5716751213742238339395416554754838804120186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree096.table
  base := (615148882117827982448767332487753166163/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-39995315375140316033752974292280000000000000)
      constant := (1312671465245150294218127912900493769122609504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58213948924112145239/20000000000000000000)
  centralHi := (72767436155140181549/25000000000000000000)
  directionLo := (292597680287490177701/100000000000000000000)
  directionHi := (146298840143745088851/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree097.table
  base := (5317836650678586648752776024783071274663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-532898992669418814366322226310000000000000)
      constant := (17507282519282652008046565846043047641471967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree097.table
  base := (332364790443337809505297344928690868913/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-40406391349692382586877848143380000000000000)
      constant := (1339997864350333995810905032799611220438163008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell232.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292597680287490177701/100000000000000000000)
  centralHi := (146298840143745088851/50000000000000000000)
  directionLo := (73529419616301455457/25000000000000000000)
  directionHi := (294117678465205821829/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree098.table
  base := (572049471661883620044648225026037426743/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (51)
      square := (4065586561503954921015235890000000000000)
      linear := (-538319774751424087594342540830000000000000)
      constant := (17867979364349728554665364124452343368406870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree098.table
  base := (143012367843112501884082832886344060753/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (305370723952963725178477717960000000000000)
      linear := (-40817467324244449140002721994480000000000000)
      constant := (1367605013641720742176172297622196743402761120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell232.Kernel098
