import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell154.Parameters
import ForestUnimodality.BinomialMassData.Q23881_45156.Batch000_049
import ForestUnimodality.BinomialMassData.Q23881_45156.Batch050_099
import ForestUnimodality.BinomialMassData.Q95549_180624.Batch000_049
import ForestUnimodality.BinomialMassData.Q95549_180624.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree000.table
  base := (194438610242888937024119399/5000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1195328761503685888190062800000000000000)
      linear := (-72449247281411435425702017000000000000)
      constant := (388877220485777874048238798000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree000.table
  base := (194438610242888937024119399/5000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1195328761503685888190062800000000000000)
      linear := (-72449247281411435425702017000000000000)
      constant := (388877220485777874048238798000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree001.table
  base := (26991966449143691532197389630419787898293/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-56786313994035636404755135534056819000000000000)
      constant := (9188889059621445964110969595515120039765608596408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree001.table
  base := (215890643481845813700898770700485816695069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-56800370313190443810996570553795569000000000000)
      constant := (9186981554507305362829834232648835580390595519983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (1247896610047016269/2500000000000000000)
  directionHi := (49915864401880650761/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree002.table
  base := (126172218094628675462554557881720217377897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-110494947231788543357028688555031019000000000000)
      constant := (5419923305556097560692585238843395491863275153779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree002.table
  base := (126125568184861147461542754358758372811679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-110523059870098158169511558594508519000000000000)
      constant := (5417972184634656645193124799947072446160139441253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1247896610047016269/2500000000000000000)
  centralHi := (49915864401880650761/100000000000000000000)
  directionLo := (2823667696588639859/4000000000000000000)
  directionHi := (17647923103678999119/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree003.table
  base := (19536811251401834553604921038483789878387/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-54734526823180483436434080525335073000000000000)
      constant := (1150812005616967200064994958512500161503797469612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree003.table
  base := (39055007605181427788457232630468557877619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-54748583142335290842675515545073823000000000000)
      constant := (1150307555607744061728618821634602595216732715222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2823667696588639859/4000000000000000000)
  centralHi := (17647923103678999119/25000000000000000000)
  directionLo := (5403550827985997207/6250000000000000000)
  directionHi := (86456813247775955313/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree004.table
  base := (51296633439758193141102885931365452810299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-217912213707294357261575794596979419000000000000)
      constant := (2412850448375977847897588875522672688666076341593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree004.table
  base := (51269123269893032712430063044889453256837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-217968438983913586886541534675934419000000000000)
      constant := (2411802462084666916036903054928585478053236976359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5403550827985997207/6250000000000000000)
  centralHi := (86456813247775955313/100000000000000000000)
  directionLo := (99831728803761301521/100000000000000000000)
  directionHi := (49915864401880650761/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree005.table
  base := (17688950827813934441941330453608033061273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-271620846945047264213849347617953619000000000000)
      constant := (1866060782816144171622628949004589636181278210822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree005.table
  base := (35357772810517281688497869413627377073953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-271691128540821301245056522716647369000000000000)
      constant := (1865393697534694307817840022984458360306699934171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99831728803761301521/100000000000000000000)
  centralHi := (49915864401880650761/50000000000000000000)
  directionLo := (13951908244783377057/12500000000000000000)
  directionHi := (111615265958267016457/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree006.table
  base := (6314720285715279639442795809827290627663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-108443160060933390388707633546309273000000000000)
      constant := (531349966614024977861883855126611609899296620188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree006.table
  base := (25243779337614975431220447975893797143221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-108471272699243005201190503585786773000000000000)
      constant := (531226191274763783257192601723524959724726564349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13951908244783377057/12500000000000000000)
  centralHi := (111615265958267016457/100000000000000000000)
  directionLo := (61134198927281315649/50000000000000000000)
  directionHi := (122268397854562631299/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree007.table
  base := (18343102300111341341807519645776248266343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-379038113420553078118396453659902019000000000000)
      constant := (1486518454378478648185620051641460749162121675901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree007.table
  base := (18331289586664040775188322624795691370227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-379136507654636729962086498798073269000000000000)
      constant := (1486383928178955261140426993861733261322767665089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61134198927281315649/50000000000000000000)
  centralHi := (122268397854562631299/100000000000000000000)
  directionLo := (33016240921049514443/25000000000000000000)
  directionHi := (132064963684198057773/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree008.table
  base := (6648220767063886408934185308761908988127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-432746746658305985070670006680876219000000000000)
      constant := (1486792199783401064803096656130324174206983880778) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree008.table
  base := (2657356900781901874792201330089007578047/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-432859197211544444320601486838786219000000000000)
      constant := (1486861195101014732798644068295128424711393149145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33016240921049514443/25000000000000000000)
  centralHi := (132064963684198057773/100000000000000000000)
  directionLo := (141183384829431992951/100000000000000000000)
  directionHi := (17647923103678999119/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree009.table
  base := (9416661034203988710709990067356000985837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-162151793298686297340981186567283473000000000000)
      constant := (521679905941154417356206498827692770373618526453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree009.table
  base := (9408467152040171998810066595456601083163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-162193962256150719559705491626499723000000000000)
      constant := (521765894960814126642255403295090888628171134547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141183384829431992951/100000000000000000000)
  centralHi := (17647923103678999119/12500000000000000000)
  directionLo := (149747593205641952281/100000000000000000000)
  directionHi := (74873796602820976141/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree010.table
  base := (3160319246159950614678549877873064182557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-540164013133811798975217112722824619000000000000)
      constant := (1704985778610961714437048728618562823737123832798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree010.table
  base := (3156749484021935068708953205777898268173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-540304576325359873037631462920212119000000000000)
      constant := (1705430221267330261757176193480265163777822007422) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149747593205641952281/100000000000000000000)
  centralHi := (74873796602820976141/50000000000000000000)
  directionLo := (15784782288606124379/10000000000000000000)
  directionHi := (157847822886061243791/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree011.table
  base := (3788721345854684436811345758116618575243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-593872646371564705927490665743798819000000000000)
      constant := (1897299429921914517345944219655282287451940288201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree011.table
  base := (1891198557509003860979707727086693212997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-594027265882267587396146450960925069000000000000)
      constant := (1897935062066257787712456931567707899033143098958) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15784782288606124379/10000000000000000000)
  centralHi := (157847822886061243791/100000000000000000000)
  directionLo := (16555219330729597961/10000000000000000000)
  directionHi := (165552193307295979611/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree012.table
  base := (1686884468891155096092324781444332473789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-215860426536439204293254739588257673000000000000)
      constant := (712095738818873625625492429547048062921040310341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree012.table
  base := (1681232866538603295345890550313718580389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-215916651813058433918220479667212673000000000000)
      constant := (712374282359623309512293856462078952866748325741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16555219330729597961/10000000000000000000)
  centralHi := (165552193307295979611/100000000000000000000)
  directionLo := (276661802392883057/160000000000000000)
  directionHi := (86456813247775955313/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree013.table
  base := (-72517583078307472571259894089844659023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-701289912847070519832037771785747219000000000000)
      constant := (2418225915296156701188278606870795586083460835339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree013.table
  base := (-38793348706115601052247484202326893107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-701472644996083016113176427042350969000000000000)
      constant := (2419272584653196350385919851376887313627159669502) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276661802392883057/160000000000000000)
  centralHi := (86456813247775955313/50000000000000000000)
  directionLo := (89987104280044159693/50000000000000000000)
  directionHi := (179974208560088319387/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree014.table
  base := (-775399664861788699870325183933220632197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-754998546084823426784311324806721419000000000000)
      constant := (2740510854558484264588922415412807245302821832242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree014.table
  base := (-1555348462727965311566821545278408669141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-755195334552990730471691415083063919000000000000)
      constant := (2741780776804031319161396984542631631456695065513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89987104280044159693/50000000000000000000)
  centralHi := (179974208560088319387/100000000000000000000)
  directionLo := (93384031378251581233/50000000000000000000)
  directionHi := (186768062756503162467/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree015.table
  base := (-2793398855716957344101126806007552315027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-269569059774192111245528292609231873000000000000)
      constant := (1033737267123205073760003353124422782692876440437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree015.table
  base := (-27974763457905793079185058669421199337/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-269639341369966148276735467707925623000000000000)
      constant := (1034239264177847569040840315061657663520539204700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93384031378251581233/50000000000000000000)
  centralHi := (186768062756503162467/100000000000000000000)
  directionLo := (19332331154003140459/10000000000000000000)
  directionHi := (193323311540031404591/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree016.table
  base := (-3835502099304639961825602982765814403129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-862415812560329240688858430848669819000000000000)
      constant := (3498834039233580616407639481954643345887177693597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree016.table
  base := (-959787259990284340198475269416383572839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-862640713666806159188721391164489819000000000000)
      constant := (3500589223112154974283690407118288405877311402508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19332331154003140459/10000000000000000000)
  centralHi := (193323311540031404591/100000000000000000000)
  directionLo := (99831728803761301521/50000000000000000000)
  directionHi := (199663457607522603043/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree017.table
  base := (-4705206083796529060568971426928842609853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-916124445798082147641131983869644019000000000000)
      constant := (3932183992354984918101400367503522254760241364529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree017.table
  base := (-2354229830007977959191395324039848183281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-916363403223713873547236379205202769000000000000)
      constant := (3934201658780961006333364136289951491817388393066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99831728803761301521/50000000000000000000)
  centralHi := (199663457607522603043/100000000000000000000)
  directionLo := (10290419066148121599/5000000000000000000)
  directionHi := (205808381322962431981/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree018.table
  base := (-271270208728511788406323036929767874101/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-323277693011945018197801845630206073000000000000)
      constant := (1466763046321883653067903204302270391939182338620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree018.table
  base := (-108565982400572730376182169869870191639/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-323362030926873862635250455748638573000000000000)
      constant := (1467527560634806924872019197047714989791468650450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10290419066148121599/5000000000000000000)
  centralHi := (205808381322962431981/100000000000000000000)
  directionLo := (211775077244147989427/100000000000000000000)
  directionHi := (52943769311036997357/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree019.table
  base := (-6014988177052176745914508401682742071529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1023541712273587961545679089911592419000000000000)
      constant := (4902346945592919208744349615713895330901217814797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree019.table
  base := (-1504389325635160012481972522678762724987/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1023808782337529302264266355286628669000000000000)
      constant := (4904929840695002572095018722120074987489402686364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211775077244147989427/100000000000000000000)
  centralHi := (52943769311036997357/25000000000000000000)
  directionLo := (217578208607277083531/100000000000000000000)
  directionHi := (54394552151819270883/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree020.table
  base := (-40560435189041861268342850353067495211/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1077250345511340868497952642932566619000000000000)
      constant := (5437689978094134781553601227161827462714663683680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree020.table
  base := (-1622985983165353754408673461326549601021/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1077531471894437016622781343327341619000000000000)
      constant := (5440575778065226395749411719104361345301920809412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217578208607277083531/100000000000000000000)
  centralHi := (54394552151819270883/25000000000000000000)
  directionLo := (223230531916534032913/100000000000000000000)
  directionHi := (111615265958267016457/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree021.table
  base := (-6862576696993981949045799982124958653017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-376986326249697925150075398651180273000000000000)
      constant := (2001920181818622714466632674385998470605266920127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree021.table
  base := (-68645853101908051634319895514871119963/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-377084720483781576993765443789351523000000000000)
      constant := (2002987627381520294973144907828448660185464625300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223230531916534032913/100000000000000000000)
  centralHi := (111615265958267016457/50000000000000000000)
  directionLo := (114371613500384849111/50000000000000000000)
  directionHi := (228743227000769698223/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree022.table
  base := (-1786177440317100095725982404306321930709/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1184667611986846682402499748974515019000000000000)
      constant := (6606091345789693330758110365458123724813051242148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree022.table
  base := (-1429295974945869554540295518552294787667/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1184976851008252445339811319408767519000000000000)
      constant := (6609623933642566338249669414449698034407242464155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114371613500384849111/50000000000000000000)
  centralHi := (228743227000769698223/100000000000000000000)
  directionLo := (117063078527895155777/50000000000000000000)
  directionHi := (46825231411158062311/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree023.table
  base := (-7345301667953618454175155155218489390641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1238376245224599589354773301995489219000000000000)
      constant := (7238290163163899883556098108428977993161449265013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree023.table
  base := (-3673429233888494845577037532229959365577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1238699540565160159698326307449480469000000000000)
      constant := (7242166801732288373261265258352804820621781384922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117063078527895155777/50000000000000000000)
  centralHi := (46825231411158062311/20000000000000000000)
  directionLo := (47877615202388486327/20000000000000000000)
  directionHi := (59847019002985607909/25000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree024.table
  base := (-7472109379167057128886751300846036883851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-430694959487450832102348951672154473000000000000)
      constant := (2634009159298319988541530948928288376744436469181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree024.table
  base := (-1494695205948266273602009461743470025431/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-430807410040689291352280431830064473000000000000)
      constant := (2635420684204485778739305876262082388467313710805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47877615202388486327/20000000000000000000)
  centralHi := (59847019002985607909/25000000000000000000)
  directionLo := (61134198927281315649/25000000000000000000)
  directionHi := (244536795709125262597/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree025.table
  base := (-1882913423839621552327378893807176074783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1345793511700105403259320408037437619000000000000)
      constant := (8597026283073721527729841350534231444169792980076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree025.table
  base := (-301314054516379727559729988519305500101/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1346144919678975588415356283530906369000000000000)
      constant := (8601632764259883593564041586896515661070524219825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61134198927281315649/25000000000000000000)
  centralHi := (244536795709125262597/100000000000000000000)
  directionLo := (124789661004701626901/50000000000000000000)
  directionHi := (249579322009403253803/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree026.table
  base := (-3764709068796313209124490984157294964709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1399502144937858310211593961058411819000000000000)
      constant := (9323053635945210053753658073378348815801229145074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree026.table
  base := (-470654128095889379879932384513274291307/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1399867609235883302773871271571619319000000000000)
      constant := (9328046076278307913982422657270865005128407157616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124789661004701626901/50000000000000000000)
  centralHi := (249579322009403253803/100000000000000000000)
  directionLo := (6363049165576021983/2500000000000000000)
  directionHi := (254521966623040879321/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree027.table
  base := (-1494002977105488189711446908987479878551/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-484403592725203739054622504693128673000000000000)
      constant := (3359971202926393393558782569412153519928091824405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree027.table
  base := (-1867732604315069764144578854308436208979/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-484530099597597005710795419870777423000000000000)
      constant := (3361768713204315250975362863914907762870552170196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6363049165576021983/2500000000000000000)
  centralHi := (254521966623040879321/100000000000000000000)
  directionLo := (259370439743327865937/100000000000000000000)
  directionHi := (129685219871663932969/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree028.table
  base := (-1471464739825124991215440169479229728361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1506919411413364124116141067100360219000000000000)
      constant := (10867441387405378317191258680747440532848762204865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree028.table
  base := (-7358122479987351663137138676763633794591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1507312988349698731490901247653045219000000000000)
      constant := (10873248214267184317079620081222530880493440462363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259370439743327865937/100000000000000000000)
  centralHi := (129685219871663932969/50000000000000000000)
  directionLo := (33016240921049514443/12500000000000000000)
  directionHi := (52825985473679223109/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree029.table
  base := (-1798652114477184054318390227030885564611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1560628044651117031068414620121334419000000000000)
      constant := (11685498320566941771524378715540771000975373848892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree029.table
  base := (-1439060897804039411950004097256890503341/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1561035677906606445849416235693758169000000000000)
      constant := (11691733718151636450533660003468689927497945630565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33016240921049514443/12500000000000000000)
  centralHi := (52825985473679223109/20000000000000000000)
  directionLo := (10752206251788226803/4000000000000000000)
  directionHi := (67201289073676417519/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree030.table
  base := (-698461504111820746975042952659270547009/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-538112225962956646006896057714102873000000000000)
      constant := (4177989253973844568525295683549543423876301154790) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree030.table
  base := (-3492610409606389434969293468764552674279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-538252789154504720069310407911490373000000000000)
      constant := (4180215356277035909200484185547319381470614813698) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10752206251788226803/4000000000000000000)
  centralHi := (67201289073676417519/25000000000000000000)
  directionLo := (273400449102791488631/100000000000000000000)
  directionHi := (34175056137848936079/12500000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree031.table
  base := (-3364826797277813904939622804051313258969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1668045311126622844972961726163282819000000000000)
      constant := (13412751575304258693126253101054392337736349165434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree031.table
  base := (-1346036047440747618104769846955315622411/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1668481057020421874566446211775184069000000000000)
      constant := (13419887188728243992947055796531883644074800788115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273400449102791488631/100000000000000000000)
  centralHi := (34175056137848936079/12500000000000000000)
  directionLo := (277919770956646794797/100000000000000000000)
  directionHi := (138959885478323397399/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree032.table
  base := (-3215833851796137209722595588839931124593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1721753944364375751925235279184257019000000000000)
      constant := (14321767196223147096255711169247642375964418382698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree032.table
  base := (-1286425014481172028224030222830750737111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1722203746577329588924961199815897019000000000000)
      constant := (14329374566704829109663044656755522225484505023615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277919770956646794797/100000000000000000000)
  centralHi := (138959885478323397399/50000000000000000000)
  directionLo := (282366769658863985903/100000000000000000000)
  directionHi := (17647923103678999119/6250000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree033.table
  base := (-761536571345333611035205737761892606329/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-591820859200709552959169610735077073000000000000)
      constant := (5086981720148494917608564413820156266726247123192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree033.table
  base := (-3046344695071744487198009462462342735021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-591975478711412434427825395952203323000000000000)
      constant := (5089679595612471275732558711684425941097360842902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282366769658863985903/100000000000000000000)
  centralHi := (17647923103678999119/6250000000000000000)
  directionLo := (143372405056350442069/50000000000000000000)
  directionHi := (286744810112700884139/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree034.table
  base := (-2856451976424192100617644534333960351143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1829171210839881565829782385226205419000000000000)
      constant := (16230227025125681754182409064301142347431094660998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree034.table
  base := (-571324792263171374332383209020905614689/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1829649125691145017641991175897322919000000000000)
      constant := (16238821449804511925282482996534658795513646326770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143372405056350442069/50000000000000000000)
  centralHi := (286744810112700884139/100000000000000000000)
  directionLo := (291057004116987061397/100000000000000000000)
  directionHi := (145528502058493530699/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree035.table
  base := (-211786373147357317290913131137014057789/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1882879844077634472782055938247179619000000000000)
      constant := (17229563619976006237085877897757275980224899524425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree035.table
  base := (-1058991445929109078933888889232930214823/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1883371815248052732000506163938035869000000000000)
      constant := (17238673424360505132968301759951787488143500223695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291057004116987061397/100000000000000000000)
  centralHi := (145528502058493530699/50000000000000000000)
  directionLo := (144192498165970667/48828125000000000)
  directionHi := (295306236243907926017/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree036.table
  base := (-2419266266446873225930348727357294926219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-645529492438462459911443163756051273000000000000)
      constant := (6086304525335959400777326934094361113923792857978) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree036.table
  base := (-4838790324559469536789335162739935828393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-645698168268320148786340383992916273000000000000)
      constant := (6089517792134642506915981917810104639870800121583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144192498165970667/48828125000000000)
  centralHi := (295306236243907926017/100000000000000000000)
  directionLo := (299495186411283904563/100000000000000000000)
  directionHi := (74873796602820976141/25000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree037.table
  base := (-4345342893504486298533479486591111671589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1990297110553140286686603044289128019000000000000)
      constant := (19318242087751325758246368659717963071247281784377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree037.table
  base := (-4345565804054130202486827620032322684997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-1990817194361868160717536140019461769000000000000)
      constant := (19328426531532756813021405168498746307078726146521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299495186411283904563/100000000000000000000)
  centralHi := (74873796602820976141/25000000000000000000)
  directionLo := (4744161713300099649/1562500000000000000)
  directionHi := (303626349651206377537/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree038.table
  base := (-152631189842397392208430996929788890307/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-2044005743790893193638876597310102219000000000000)
      constant := (20407519871882955910628974048494853797919781358775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree038.table
  base := (-3815972354374619535534900074597908265317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-2044539883918775875076051128060174719000000000000)
      constant := (20418263634006137569259486995918605592124843324281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4744161713300099649/1562500000000000000)
  centralHi := (303626349651206377537/100000000000000000000)
  directionLo := (15385102674462686789/5000000000000000000)
  directionHi := (307702053489253735781/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree039.table
  base := (-1625211529049981457681701868090053512477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-699238125676215366863716716777025473000000000000)
      constant := (7175574097029210466362196065506170310838564142774) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree039.table
  base := (-3250589368183990586770017590927438847127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-699420857825227863144855372033629223000000000000)
      constant := (7179346690309997071898253808554179058687516515537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15385102674462686789/5000000000000000000)
  centralHi := (307702053489253735781/100000000000000000000)
  directionLo := (62344894655614104451/20000000000000000000)
  directionHi := (19482779579879407641/6250000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree040.table
  base := (-529952156255093064092134858192878386119/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-2151423010266399007543423703352050619000000000000)
      constant := (22675828616931830730121986309480301621841615588335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree040.table
  base := (-2649904289407635970251728180689851660573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-2151985263032591303793081104141600619000000000000)
      constant := (22687735135439233003907923530004002689204067049489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62344894655614104451/20000000000000000000)
  centralHi := (19482779579879407641/6250000000000000000)
  directionLo := (15784782288606124379/5000000000000000000)
  directionHi := (315695645772122487581/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree041.table
  base := (-251775431294832167553225163027599266879/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-2205131643504151914495697256373024819000000000000)
      constant := (23854821409690289067431663025148210272951214178776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree041.table
  base := (-251790900675866206459690503918637423199/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-2205707952589499018151596092182313569000000000000)
      constant := (23867331406814837475619543232190994377481663344856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15784782288606124379/5000000000000000000)
  centralHi := (315695645772122487581/100000000000000000000)
  directionLo := (319617481184093519607/100000000000000000000)
  directionHi := (39952185148011689951/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree042.table
  base := (-336024116496340138696392485487804714017/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-752946758913968273815990269797999673000000000000)
      constant := (8354561998856292862651926563196798929742090444508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree042.table
  base := (-268840624672786294545763234661288682021/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-753143547382135577503370360074342173000000000000)
      constant := (8358938076325597362483551486392224747898976892255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319617481184093519607/100000000000000000000)
  centralHi := (39952185148011689951/12500000000000000000)
  directionLo := (161745886962738028553/50000000000000000000)
  directionHi := (323491773925476057107/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree043.table
  base := (-639730428639605279786966238737882583777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-2312548909979657728400244362414973219000000000000)
      constant := (26302410032711703238456793998835889080984683065061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree043.table
  base := (-79977787300935739999173113613960560831/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-2313153331703314446868626068263739469000000000000)
      constant := (26316171271740064175286853603712609460533158229464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161745886962738028553/50000000000000000000)
  centralHi := (323491773925476057107/100000000000000000000)
  directionLo := (327320212202727020959/100000000000000000000)
  directionHi := (2045751326267043881/625000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree044.table
  base := (98650166926641289066359751450732871739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-2366257543217410635352517915435947419000000000000)
      constant := (27570983131857740613222342778241528678913038691673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree044.table
  base := (9857107732483602337382239744051165771/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-2366876021260222161227141056304452419000000000000)
      constant := (27585392161698844310015230042201000879808931258970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327320212202727020959/100000000000000000000)
  centralHi := (2045751326267043881/625000000000000000)
  directionLo := (331104386614591959221/100000000000000000000)
  directionHi := (165552193307295979611/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree045.table
  base := (870839616706054586788250321858321679677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-806655392151721180768263822818973873000000000000)
      constant := (9623132185198822544339419866814116795290590185413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree045.table
  base := (54423222785487967448768749603135188217/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-806866236939043291861885348115055123000000000000)
      constant := (9628156057229662648793379628897408316994992458768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331104386614591959221/100000000000000000000)
  centralHi := (165552193307295979611/50000000000000000000)
  directionLo := (33484579787480104937/10000000000000000000)
  directionHi := (334845797874801049371/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree046.table
  base := (419166213255597935291009341957183449453/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-2473674809692916449257065021477895819000000000000)
      constant := (30197642951925252188777729151515831887399089250684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree046.table
  base := (167660632691457280796662215861304196411/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-2474321400374037589944171032385878319000000000000)
      constant := (30213391959532303798541534526624933485322668603770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33484579787480104937/10000000000000000000)
  centralHi := (334845797874801049371/100000000000000000000)
  directionLo := (84636465941622591671/25000000000000000000)
  directionHi := (67709172753298073337/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree047.table
  base := (2515980266556860968110225688302337471039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-2527383442930669356209338574498870019000000000000)
      constant := (31555716135286408080885450024988893089304834536773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree047.table
  base := (503185991359987201605995786923984167503/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-2528044089930945304302686020426591269000000000000)
      constant := (31572157348241700704792708731670989932477501820105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84636465941622591671/25000000000000000000)
  centralHi := (67709172753298073337/20000000000000000000)
  directionLo := (342205925419747796197/100000000000000000000)
  directionHi := (171102962709873898099/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree048.table
  base := (3388663349895146204400388425357234797629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-860364025389474087720537375839948073000000000000)
      constant := (10981203633834287967972439850712864934107107439301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree048.table
  base := (135544804903653870715432498272395441697/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-860588926495951006220400336155768073000000000000)
      constant := (10986919713702468596732929853686755066231479169825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342205925419747796197/100000000000000000000)
  centralHi := (171102962709873898099/50000000000000000000)
  directionLo := (276661802392883057/80000000000000000)
  directionHi := (345827252991103821251/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree049.table
  base := (858922206451014894127769774961471624919/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-2634800709406175170113885680540818419000000000000)
      constant := (34361322872075536063146908832963023850213364769665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree049.table
  base := (4294573906478998137448688093440935980257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-2635489469044760733019715996508017169000000000000)
      constant := (34379192966128679125948024058321000762870859350299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276661802392883057/80000000000000000)
  centralHi := (345827252991103821251/100000000000000000000)
  directionLo := (349411050813164555323/100000000000000000000)
  directionHi := (87352762703291138831/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree050.table
  base := (5233736595734367405528790759973933305871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-2688509342643928077066159233561792619000000000000)
      constant := (35808848363183969797331199934543013631117586156597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree050.table
  base := (5233704723536327189472971728325972916539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-2689212158601668447378230984548730119000000000000)
      constant := (35827455145133941761123613572661071806387845405273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349411050813164555323/100000000000000000000)
  centralHi := (87352762703291138831/25000000000000000000)
  directionLo := (352958462073579982379/100000000000000000000)
  directionHi := (17647923103678999119/5000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree051.table
  base := (6205967080816367368225908226707589343611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-914072658627226994672810928860922273000000000000)
      constant := (12428728091823635671647234278710410270438130830259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree051.table
  base := (6205939729720157218521641237218239184543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-914311616052858720578915324196481023000000000000)
      constant := (12435180861223769206462667915890753023485551067767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352958462073579982379/100000000000000000000)
  centralHi := (17647923103678999119/5000000000000000000)
  directionLo := (71294114614976104579/20000000000000000000)
  directionHi := (22279410817180032681/6250000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree052.table
  base := (1802810275877415501223617705657162859329/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-2795926609119433890970706339603741019000000000000)
      constant := (38793328001313270835541412313395247448783462399212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree052.table
  base := (1442243528243321853482514844239700973243/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-2796657537715483876095260960630156019000000000000)
      constant := (38813452678373292229003466732512417416108780371005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71294114614976104579/20000000000000000000)
  centralHi := (22279410817180032681/6250000000000000000)
  directionLo := (359948417120176638773/100000000000000000000)
  directionHi := (179974208560088319387/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree053.table
  base := (4124753509406562747701544083421190172747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (1179594)
      previous := (589797)
      next := (589797)
      square := (18076956860220241687098319724400000000000000)
      linear := (-1014466088414804840841217476904491000000000000)
      constant := (14357521305377440163303793555122724067964905762) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree053.table
  base := (1031185862481616847453224926947764247283/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (1179594)
      previous := (589797)
      next := (589797)
      square := (18076956860220241687098319724400000000000000)
      linear := (-1014731301983763471147659647088241000000000000)
      constant := (14364963773236944548844968313361449434693286472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359948417120176638773/100000000000000000000)
  centralHi := (179974208560088319387/50000000000000000000)
  directionLo := (363392978064116707781/100000000000000000000)
  directionHi := (181696489032058353891/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree054.table
  base := (9320721375559529196410014590160188003467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-967781291864979901625084481881896473000000000000)
      constant := (13965676822039723049974818218224166228700865305923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree054.table
  base := (2330176032413805819476172523326350468959/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-968034305609766434937430312237193973000000000000)
      constant := (13972910807661933103215892684785508704299754776284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363392978064116707781/100000000000000000000)
  centralHi := (181696489032058353891/50000000000000000000)
  directionLo := (73361038712737578779/20000000000000000000)
  directionHi := (45850649195460986737/12500000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree055.table
  base := (10424847616408562235836180018399348684721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-2957052508832692611827526998666663619000000000000)
      constant := (43493585806280739051770176947553737986846731233547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree055.table
  base := (5212416419173827503722362809165914103997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-2957825606386207019170805924752294869000000000000)
      constant := (43516098680052580037805241196374266664012486572958) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73361038712737578779/20000000000000000000)
  centralHi := (45850649195460986737/12500000000000000000)
  directionLo := (370185958059299540901/100000000000000000000)
  directionHi := (185092979029649770451/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree056.table
  base := (5780927492047334532836951462865733239289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3010761142070445518779800551687637819000000000000)
      constant := (45119942060705704390941493823871725955863498079046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree056.table
  base := (92494738599372112754609217900570010827/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3011548295943114733529320912793007819000000000000)
      constant := (45143280706028503760435146201539111082615806161125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370185958059299540901/100000000000000000000)
  centralHi := (185092979029649770451/50000000000000000000)
  directionLo := (93384031378251581233/25000000000000000000)
  directionHi := (373536125513006324933/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree057.table
  base := (12731717601205998546988203816366265653367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1021489925102732808577358034902870673000000000000)
      constant := (15592032710036163294415973304870229104800572139023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree057.table
  base := (318292669014276516515122888231774402193/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1021756995166674149295945300277906923000000000000)
      constant := (15600092467897602481004070506793137682322074024680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93384031378251581233/25000000000000000000)
  centralHi := (373536125513006324933/100000000000000000000)
  directionLo := (188428255963811960523/50000000000000000000)
  directionHi := (376856511927623921047/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree058.table
  base := (696720684798129688115336697473782121099/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3118178408545951332684347657729586219000000000000)
      constant := (48462053089612844666397072686779432613736418343860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree058.table
  base := (6967202207741626097357424941962167614939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3118993675056930162246350888874433719000000000000)
      constant := (48487087849952016024432553073757365315328178988146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188428255963811960523/50000000000000000000)
  centralHi := (376856511927623921047/100000000000000000000)
  directionLo := (95036974416948075081/25000000000000000000)
  directionHi := (15205915906711692013/4000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree059.table
  base := (948120309426879184992542448083409545553/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3171887041783704239636621210750560419000000000000)
      constant := (50177806161080620958760072378393985029789696565936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree059.table
  base := (15169917008334569657895307899752648644599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3172716364613837876604865876915146669000000000000)
      constant := (50203711268206237784905465908397176853765428331693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95036974416948075081/25000000000000000000)
  centralHi := (15205915906711692013/4000000000000000000)
  directionLo := (383411029601691587311/100000000000000000000)
  directionHi := (23963189350105724207/6250000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree060.table
  base := (8219117977240044265804669673446373013267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1075198558340485715529631587923844873000000000000)
      constant := (17307785563276925925040563313639108163609799924246) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree060.table
  base := (16438229159021550498799611809813504083013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1075479684723581863654460288318619873000000000000)
      constant := (17316715668366959974264743206664502050047654109197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383411029601691587311/100000000000000000000)
  centralHi := (23963189350105724207/6250000000000000000)
  directionLo := (386646623080062809181/100000000000000000000)
  directionHi := (193323311540031404591/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree061.table
  base := (8869666870350513356647242515534796006321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3279304308259210053541168316792508819000000000000)
      constant := (53698704125052071128841480138765214123730182569494) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree061.table
  base := (221741599103025298965957939792787130879/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3280161743727653305321895852996572569000000000000)
      constant := (53726394510967825996307828681149799455650222052240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386646623080062809181/100000000000000000000)
  centralHi := (193323311540031404591/50000000000000000000)
  directionLo := (97463840941847214947/25000000000000000000)
  directionHi := (389855363767388859789/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree062.table
  base := (19073207400463514806929852951217362591039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3333012941496962960493441869813483019000000000000)
      constant := (55503848003323402644699221019025060220570170376773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree062.table
  base := (19073202430143997060035952206675754911683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3333884433284561019680410841037285519000000000000)
      constant := (55532453323370564222078109185045472278131034063281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97463840941847214947/25000000000000000000)
  centralHi := (389855363767388859789/100000000000000000000)
  directionLo := (393037909338514101753/100000000000000000000)
  directionHi := (196518954669257050877/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree063.table
  base := (39921577647528177742871928998704093057/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1128907191578238622481905140944819073000000000000)
      constant := (19112929311582925258056425995097747720953569476096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree063.table
  base := (20439843506446486270083304781600322003611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1129202374280489578012975276359332823000000000000)
      constant := (19122774351086891721965746983863279374025550370259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393037909338514101753/100000000000000000000)
  centralHi := (196518954669257050877/50000000000000000000)
  directionLo := (396194891052594173317/100000000000000000000)
  directionHi := (198097445526297086659/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree064.table
  base := (10919623541937097818048875090893682747507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3440430207972468774397988975855431419000000000000)
      constant := (59203523591292034608592247286460150268422500692098) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree064.table
  base := (10919621726138402590261361902102294683481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3441329812398376448397440817118711419000000000000)
      constant := (59234003373331260740447495196988977604035354809734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396194891052594173317/100000000000000000000)
  centralHi := (198097445526297086659/50000000000000000000)
  directionLo := (99831728803761301521/25000000000000000000)
  directionHi := (79865383043009041217/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree065.table
  base := (11635699444300847905208592707591710566729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3494138841210221681350262528876405619000000000000)
      constant := (61098054696962375043836071902204625181493810503206) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree065.table
  base := (11635697892758499946043362151366220466911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3495052501955284162755955805159424369000000000000)
      constant := (61129494008218663830285362231027810233091312007754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99831728803761301521/25000000000000000000)
  centralHi := (79865383043009041217/20000000000000000000)
  directionLo := (40243456453708202633/10000000000000000000)
  directionHi := (402434564537082026331/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree066.table
  base := (154601860647590067847603825711638627989/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1182615824815991529434178693965793273000000000000)
      constant := (21007460339852330285903772658205073398780379222560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree066.table
  base := (12368147526377303399275995188998227946669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1182925063837397292371490264400045773000000000000)
      constant := (21018264908753052700433142413029231161725712054122) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40243456453708202633/10000000000000000000)
  centralHi := (402434564537082026331/100000000000000000000)
  directionLo := (10137959985036985193/2500000000000000000)
  directionHi := (405518399401479407721/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree067.table
  base := (26233938930048272446514823783635761674767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3601556107685727495254809634918354019000000000000)
      constant := (64976502363713804803681646984947141538525271266869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree067.table
  base := (5246787333205738375801451449076652360077/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3602497881069099591472985781240850269000000000000)
      constant := (65009905332553836980087831091107005499844087595195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10137959985036985193/2500000000000000000)
  centralHi := (405518399401479407721/100000000000000000000)
  directionLo := (408578959042343136711/100000000000000000000)
  directionHi := (51072369880292892089/12500000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree068.table
  base := (27764318698684254088574427754888994851117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3655264740923480402207083187939328219000000000000)
      constant := (66960418565066430942212677762137053296995839676319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree068.table
  base := (27764316765484014704971808054185684712857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3656220570626007305831500769281563219000000000000)
      constant := (66994825663134092906641815695544262219494314778499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408578959042343136711/100000000000000000000)
  centralHi := (51072369880292892089/12500000000000000000)
  directionLo := (411616762645924863961/100000000000000000000)
  directionHi := (205808381322962431981/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree069.table
  base := (14663716877092545662652162499240499272781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1236324458053744436386452246986767473000000000000)
      constant := (22991376495108830607733196326146614350943912119978) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree069.table
  base := (1173097284152869737696345530314737889243/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1236647753394305006730005252440758723000000000000)
      constant := (23003185193351008374714583080833779988934604051675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411616762645924863961/100000000000000000000)
  centralHi := (205808381322962431981/50000000000000000000)
  directionLo := (12957259699338895973/3125000000000000000)
  directionHi := (414632310378844671137/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree070.table
  base := (3865410169712329048895267193814248417873/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3762682007398986216111630293981276619000000000000)
      constant := (71017635008146159441601195287963505185421543212888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree070.table
  base := (15461639974543823265318189088111199585427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3763665949739822734548530745362989119000000000000)
      constant := (71054094967255832775100485882508526175909257542978) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12957259699338895973/3125000000000000000)
  centralHi := (414632310378844671137/100000000000000000000)
  directionLo := (208813042174743911737/50000000000000000000)
  directionHi := (16705043373979512939/4000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree071.table
  base := (32551859204913829896569026289561466854979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84270000000000000000000000000000000000000000
      center := (657306)
      previous := (328653)
      next := (328653)
      square := (10073035473191560979777659215600000000000000)
      linear := (-757070152873782805606804968657459000000000000)
      constant := (14499292806117264871772894482911804731186908033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree071.table
  base := (32551858002887635641441369434238266041219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84270000000000000000000000000000000000000000
      center := (657306)
      previous := (328653)
      next := (328653)
      square := (10073035473191560979777659215600000000000000)
      linear := (-757268129199906853582036447808709000000000000)
      constant := (14506733530471249692824187066746802367929352513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208813042174743911737/50000000000000000000)
  centralHi := (16705043373979512939/4000000000000000000)
  directionLo := (420598549507808519671/100000000000000000000)
  directionHi := (52574818688476064959/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree072.table
  base := (17106582678558854030949030100344890785707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1290033091291497343338725800007741673000000000000)
      constant := (25064676495147300005206738026418714729624307808966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree072.table
  base := (85532910828955915590944310700256637553/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1290370442951212721088520240481471673000000000000)
      constant := (25077533925820085397427203433875176850948890582800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420598549507808519671/100000000000000000000)
  centralHi := (52574818688476064959/12500000000000000000)
  directionLo := (84710030897659195771/20000000000000000000)
  directionHi := (52943769311036997357/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree073.table
  base := (35907198183190613167446952084085801235759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3923807907112244936968450953044199219000000000000)
      constant := (77326918288269672964962965211349042723746268849813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree073.table
  base := (35907197308401141891588344796658031455611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3924834018410545877624075709485127969000000000000)
      constant := (77366569049213848290536599361903729553231303274777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84710030897659195771/20000000000000000000)
  centralHi := (52943769311036997357/12500000000000000000)
  directionLo := (426481332400430307859/100000000000000000000)
  directionHi := (21324066620021515393/5000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree074.table
  base := (1881697815540215742353774962847699244379/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3977516540349997843920724506065173419000000000000)
      constant := (79489601385823252070268983041589188497194736403060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree074.table
  base := (376339555647422478338452473185035904803/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-3978556707967453591982590697525840919000000000000)
      constant := (79530345484227451271655579411611283189048517512100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426481332400430307859/100000000000000000000)
  centralHi := (21324066620021515393/5000000000000000000)
  directionLo := (429392501570571516513/100000000000000000000)
  directionHi := (214696250785285758257/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree075.table
  base := (19696719292681431916840628911473443837887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1343741724529250250290999353028715873000000000000)
      constant := (27227359576351605342175159110773562201262977045806) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree075.table
  base := (3939343794920184325118919585192557773523/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1344093132508120435447035228522184623000000000000)
      constant := (27241310344529615405399743480800860787403494053870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429392501570571516513/100000000000000000000)
  centralHi := (214696250785285758257/50000000000000000000)
  directionLo := (216142033119439888281/50000000000000000000)
  directionHi := (432284066238879776563/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree076.table
  base := (5148205504432220691710572575181374868021/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4084933806825503657825271612107121819000000000000)
      constant := (83904350276698439479290425726429954539804721333176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree076.table
  base := (20592821746552451700024746687539429967501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4086002087081269020699620673607266819000000000000)
      constant := (83947325656148226954823124254446255735270872006014) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216142033119439888281/50000000000000000000)
  centralHi := (432284066238879776563/100000000000000000000)
  directionLo := (217578208607277083531/50000000000000000000)
  directionHi := (435156417214554167063/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree077.table
  base := (43010571843803929156955272430284911032991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4138642440063256564777545165128096019000000000000)
      constant := (86156415994035437408258066937418578881881351406437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree077.table
  base := (43010571381506347339732560469851494721489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4139724776638176735058135661647979769000000000000)
      constant := (86200529317286313272010560662416143014101676514923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217578208607277083531/50000000000000000000)
  centralHi := (435156417214554167063/100000000000000000000)
  directionLo := (109502483123099219461/25000000000000000000)
  directionHi := (87601986498479375569/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree078.table
  base := (224341106613934151167849712550325248457/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1397450357767003157243272906049690073000000000000)
      constant := (29479425283951865397794049690989870036123621846600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree078.table
  base := (22434110464397121075423347195230182223641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1397815822065028149805550216562897573000000000000)
      constant := (29494513995959320884031930000692695083000104710658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109502483123099219461/25000000000000000000)
  centralHi := (87601986498479375569/20000000000000000000)
  directionLo := (55105622229182098417/12500000000000000000)
  directionHi := (440844977833456787337/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree079.table
  base := (46758591893889286230002982037199419275893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4246059706538762378682092271170044419000000000000)
      constant := (90749929825583212612426959773622796823195507517751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree079.table
  base := (23379295779082370944810008011727803191977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4247170155751992163775165637729405669000000000000)
      constant := (90796363643420255279837489356350021752182802584678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55105622229182098417/12500000000000000000)
  centralHi := (440844977833456787337/100000000000000000000)
  directionLo := (221830953656138767319/50000000000000000000)
  directionHi := (443661907312277534639/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree080.table
  base := (24340841535191159141250047473949108007153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4299768339776515285634365824191018619000000000000)
      constant := (93091377894541792871667932619160243820683238133142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree080.table
  base := (48681682784354323485379991569996412021497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4300892845308899878133680625770118619000000000000)
      constant := (93138994263298950666587292658482558965854087458979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221830953656138767319/50000000000000000000)
  centralHi := (443661907312277534639/100000000000000000000)
  directionLo := (446461063833068065827/100000000000000000000)
  directionHi := (111615265958267016457/25000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree081.table
  base := (50637494442762229563295930909320674186533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1451158991004756064195546459070664273000000000000)
      constant := (31820873347111804103829101283470085540925244804077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree081.table
  base := (10127498839822478398473676688694521184623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1451538511621935864164065204603610523000000000000)
      constant := (31837144610057118851999250825456680075366709406435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446461063833068065827/100000000000000000000)
  centralHi := (111615265958267016457/25000000000000000000)
  directionLo := (112310694904231464211/25000000000000000000)
  directionHi := (89848555923385171369/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree082.table
  base := (3289126604156137142306457850520992436493/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4407185606252021099538912930232967019000000000000)
      constant := (97863656251328226774964100415358727211026207071216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree082.table
  base := (52626025458979363114906877794598514122387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4408338224422715306850710601851544519000000000000)
      constant := (97913682329447135673179216128789688514990659810209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112310694904231464211/25000000000000000000)
  centralHi := (89848555923385171369/20000000000000000000)
  directionLo := (90401475332414514769/20000000000000000000)
  directionHi := (226003688331036286923/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree083.table
  base := (13661819112930944744546047117207232764741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4460894239489774006491186483253941219000000000000)
      constant := (100294486512206563207067099541320372570902837614748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree083.table
  base := (54647276275004347543229568833967864265157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4462060913979623021209225589892257469000000000000)
      constant := (100345739748851507742151947886493290153941051794599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90401475332414514769/20000000000000000000)
  centralHi := (226003688331036286923/50000000000000000000)
  directionLo := (454755167178907034863/100000000000000000000)
  directionHi := (28422197948681689679/6250000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree084.table
  base := (5670124655456397802609315620831424030027/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1504867624242508971147820012091638473000000000000)
      constant := (34251703604536829241178944728685340204758433945630) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree084.table
  base := (56701246404094625440513253504055710601033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1505261201178843578522580192644323473000000000000)
      constant := (34269202026019256925412913604744411760775718854577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454755167178907034863/100000000000000000000)
  centralHi := (28422197948681689679/6250000000000000000)
  directionLo := (91497290800307879289/20000000000000000000)
  directionHi := (228743227000769698223/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree085.table
  base := (58787935769838277615563581643719919601133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4568311505965279820395733589295889619000000000000)
      constant := (105245529146823828071413574008438655759405367614431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree085.table
  base := (29393967820868974300962219054629343725011/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4569506293093438449926255565973683369000000000000)
      constant := (105299281308378140783988428249238989255156471721154) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91497290800307879289/20000000000000000000)
  centralHi := (228743227000769698223/50000000000000000000)
  directionLo := (230100765488671048673/50000000000000000000)
  directionHi := (460201530977342097347/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree086.table
  base := (30453671962460715984287471929350215167743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4622020139203032727348007142316863819000000000000)
      constant := (107765741504513376289047397823537814938269625371402) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree086.table
  base := (951677247123121948563356758439176303333/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4623228982650346164284770554014396319000000000000)
      constant := (107820765432503654850434800087657201727165184309184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230100765488671048673/50000000000000000000)
  centralHi := (460201530977342097347/100000000000000000000)
  directionLo := (462900683335935996969/100000000000000000000)
  directionHi := (46290068333593599697/10000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree087.table
  base := (1261189417491565452872936905697503474947/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1558576257480261878100093565112612673000000000000)
      constant := (36771915960169822928937939504029041048916839302150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree087.table
  base := (63059470781772352990733092987671072203911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1558983890735751292881095180685036423000000000000)
      constant := (36790686148095117104196889393871065687318582220959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462900683335935996969/100000000000000000000)
  centralHi := (46290068333593599697/10000000000000000000)
  directionLo := (11639604700973080887/2500000000000000000)
  directionHi := (465584188038923235481/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree088.table
  base := (16311079124154503462089043294820632600041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4729437405678538541252554248358812219000000000000)
      constant := (112895548269621379033522305486247410109641879603148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree088.table
  base := (32622158208820414274797678157271766193967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4730674361764161593001800530095822219000000000000)
      constant := (112953160338550176417682771140551335563910357002538) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11639604700973080887/2500000000000000000)
  centralHi := (465584188038923235481/100000000000000000000)
  directionLo := (468252314111580623109/100000000000000000000)
  directionHi := (46825231411158062311/10000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree089.table
  base := (2108183771507438593824023083724149768563/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4783146038916291448204827801379786419000000000000)
      constant := (115505142667481999585991628173695314829749644846112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree089.table
  base := (2698475224841507371046800264796801272813/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4784397051321069307360315518136535169000000000000)
      constant := (115564071110946106423636850725896174751558538904775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468252314111580623109/100000000000000000000)
  centralHi := (46825231411158062311/10000000000000000000)
  directionLo := (470905322957637952761/100000000000000000000)
  directionHi := (235452661478818976381/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree090.table
  base := (8714020420368468769759233252509344801379/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1612284890718014785052367118133586873000000000000)
      constant := (39381510356805722167480069876447829354234384584408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree090.table
  base := (69712163305775327441637669962778907054637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1612706580292659007239610168725749373000000000000)
      constant := (39401596919270616231407715473736842087903952153653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470905322957637952761/100000000000000000000)
  centralHi := (235452661478818976381/50000000000000000000)
  directionLo := (473543468658183731371/100000000000000000000)
  directionHi := (118385867164545932843/25000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree091.table
  base := (71995164447980529417304583558509382960967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4890563305391797262109374907421734819000000000000)
      constant := (120813713475335716452112558527122316737689039370269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree091.table
  base := (71995164399345628808302313756338378612961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4891842430434884736077345494217961069000000000000)
      constant := (120875319276067221137802807250319378609786540051227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473543468658183731371/100000000000000000000)
  centralHi := (118385867164545932843/25000000000000000000)
  directionLo := (476166998255665733699/100000000000000000000)
  directionHi := (4761669982556657337/1000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree092.table
  base := (74310883882116239441956171574347493321861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4944271938629550169061648460442709019000000000000)
      constant := (123512689879636987132198383954227815483491769463527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree092.table
  base := (7431088384074895414716426823915674250139/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-4945565119991792450435860482258674019000000000000)
      constant := (123575656663120928365513373138924119153177495404730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476166998255665733699/100000000000000000000)
  centralHi := (4761669982556657337/1000000000000000000)
  directionLo := (47877615202388486327/10000000000000000000)
  directionHi := (478776152023884863271/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree093.table
  base := (598900950108197307939540770755936839867/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1665993523955767692004640671154561073000000000000)
      constant := (42080486760377664495724034893283458566197860162944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree093.table
  base := (76659321578667727511585637473079223897643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1666429269849566721598125156766462323000000000000)
      constant := (42101934305597657911043553774052897471654463581667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47877615202388486327/10000000000000000000)
  centralHi := (478776152023884863271/100000000000000000000)
  directionLo := (481371163724817490061/100000000000000000000)
  directionHi := (240685581862408745031/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree094.table
  base := (19760119399961783234736479021009209191443/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-5051689205105055982966195566484657419000000000000)
      constant := (129000024677982951309318297863670742630986234806404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree094.table
  base := (19760119392482462382059857480926945215729/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-5053010499105607879152890458340099919000000000000)
      constant := (129065758035249384571021358922857161633776569178412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481371163724817490061/100000000000000000000)
  centralHi := (240685581862408745031/50000000000000000000)
  directionLo := (241976130426521606223/50000000000000000000)
  directionHi := (483952260853043212447/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree095.table
  base := (40727175901826912274273499338054475732133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-5105397838342808889918469119505631619000000000000)
      constant := (131788383068638189219257941038964125881690412062862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree095.table
  base := (8145435177821597107770811801454008433233/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-5106733188662515593511405446380812869000000000000)
      constant := (131855522016947296514682605824883226584260134891310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241976130426521606223/50000000000000000000)
  centralHi := (483952260853043212447/100000000000000000000)
  directionLo := (19460786594740056099/4000000000000000000)
  directionHi := (121629916217125350619/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree096.table
  base := (41950472097299321047618475253019811192441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1719702157193520598956914224175535273000000000000)
      constant := (44868845150598600278115823122201227381666112165058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree096.table
  base := (83900944172971922805531628582840420283431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16926057273452886299686393368613200000000000000)
      linear := (-1720151959406474435956640144807175273000000000000)
      constant := (44891698286862917652991025136342260209244410859839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19460786594740056099/4000000000000000000)
  centralHi := (121629916217125350619/25000000000000000000)
  directionLo := (489073591418250525193/100000000000000000000)
  directionHi := (244536795709125262597/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree097.table
  base := (3455210189875132874745814911258301915379/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-5212815104818314703823016225547580019000000000000)
      constant := (137454481826359650429915647148097290794859275428825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree097.table
  base := (43190127364246871232233232022672078103567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-5214178567776331022228435422462238769000000000000)
      constant := (137524476565081836555721004545497467460041249336938) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell154.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489073591418250525193/100000000000000000000)
  centralHi := (244536795709125262597/50000000000000000000)
  directionLo := (245807125273929350827/50000000000000000000)
  directionHi := (98322850109571740331/20000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree098.table
  base := (88892283438784728444315882391584381992629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-5266523738056067610775289778568554219000000000000)
      constant := (140332222191407565407106907029512850529828550182903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree098.table
  base := (2222307085578947724836863273419540078423/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (3313479546)
      previous := (1656739773)
      next := (1656739773)
      square := (50778171820358658899059180105839600000000000000)
      linear := (-5267901257333238736586950410502951719000000000000)
      constant := (140403667129507969167128317077577243802154152018440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell154.Kernel098
