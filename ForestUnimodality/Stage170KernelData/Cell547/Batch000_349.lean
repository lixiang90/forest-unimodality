import ForestUnimodality.FiniteKernelDegreeCertificate
import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell547.Parameters
import ForestUnimodality.BinomialMassData.Q129_209.Batch000_049
import ForestUnimodality.BinomialMassData.Q129_209.Batch050_099
import ForestUnimodality.BinomialMassData.Q33_53.Batch000_049
import ForestUnimodality.BinomialMassData.Q33_53.Batch050_099

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree000.table
  base := (313488272133371080357733259/25000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (387)
      previous := (0)
      next := (240)
      square := (4626160663026353987714589540000000000000)
      linear := (-12864871123353127380095628490000000000000)
      constant := (2382510868213620210718772768400000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree000.table
  base := (313488272133371080357733259/25000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (1089)
      previous := (0)
      next := (660)
      square := (12904553428441934807835433980000000000000)
      linear := (-35886219449353460586582542630000000000000)
      constant := (6645951369227466903583945090800000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree000.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel000

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree001.table
  base := (50870133980666875347798640138498351033683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-42705382674257632463973855013030000000000000)
      constant := (4466423683237448260134611995792862943004614246) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree001.table
  base := (101534805457147307467755802486981354951721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-2753670157092901108406013402070000000000000)
      constant := (286660665821588908744315967198460626059384289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree001.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel001

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (48472575768547656679/100000000000000000000)
  directionHi := (1211814394213691417/2500000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree002.table
  base := (3296787305662650935382082127828279727073/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-55834426635926425081107860127550000000000000)
      constant := (3652891806891894996206815626040537168956892825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree002.table
  base := (82085181449185892425605800404375516530249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-3605370683370068805723152044750000000000000)
      constant := (234006373376954331694371917572430825933469441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree002.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel002

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48472575768547656679/100000000000000000000)
  centralHi := (1211814394213691417/2500000000000000000)
  directionLo := (68550574055037547141/100000000000000000000)
  directionHi := (34275287027518773571/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree003.table
  base := (16660467325089580056244947038432223072749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-68963470597595217698241865242070000000000000)
      constant := (3002215325930581523235252709499501744162996276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree003.table
  base := (6623343315295413913839366957351346963193/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-4457071209647236503040290687430000000000000)
      constant := (191988817907835290250113736504029336196091370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree003.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel003

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68550574055037547141/100000000000000000000)
  centralHi := (34275287027518773571/50000000000000000000)
  directionLo := (83956964004856561683/100000000000000000000)
  directionHi := (20989241001214140421/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree004.table
  base := (53751768837531945534715302296213852590397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-82092514559264010315375870356590000000000000)
      constant := (2485780603798634995877265893887117295001131357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree004.table
  base := (26654234131771796037770291032497499385089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-5308771735924404200357429330110000000000000)
      constant := (158722901129743932826145496339570951545430002) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree004.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel004

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83956964004856561683/100000000000000000000)
  centralHi := (20989241001214140421/25000000000000000000)
  directionLo := (96945151537095313359/100000000000000000000)
  directionHi := (1211814394213691417/1250000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree005.table
  base := (43209979737096280255632070216548051700123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-95221558520932802932509875471110000000000000)
      constant := (2080026042876058262804830422917085446313072763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree005.table
  base := (2672431865509844151521381135649480849379/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-6160472262201571897674567972790000000000000)
      constant := (132659805238454203243580425938080267294489776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree005.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel005

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96945151537095313359/100000000000000000000)
  centralHi := (1211814394213691417/1250000000000000000)
  directionLo := (108387974462981672827/100000000000000000000)
  directionHi := (27096993615745418207/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree006.table
  base := (17291511651156236488156299725841034189197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-108350602482601595549643880585630000000000000)
      constant := (1766016860210601555515818808310944428836628314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree006.table
  base := (8535601700338664323496837377156223306467/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-7012172788478739594991706615470000000000000)
      constant := (112556965978781700784130796017107325071463212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree006.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel006

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108387974462981672827/100000000000000000000)
  centralHi := (27096993615745418207/25000000000000000000)
  directionLo := (5936653857566895549/5000000000000000000)
  directionHi := (118733077151337910981/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree007.table
  base := (214978727856651950158806683179660950357/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-121479646444270388166777885700150000000000000)
      constant := (1528306477166227389277708183088368556485646976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree007.table
  base := (3387353420588453836778325817956365766301/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-7863873314755907292308845258150000000000000)
      constant := (97402773241303819549185116309905451500316072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree007.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel007

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5936653857566895549/5000000000000000000)
  centralHi := (118733077151337910981/100000000000000000000)
  directionLo := (64123190445156333759/50000000000000000000)
  directionHi := (128246380890312667519/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree008.table
  base := (10862246606627027847836418477012578405683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-134608690405939180783911890814670000000000000)
      constant := (1354303927881454036725306713515092874677278246) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree008.table
  base := (10667602490603495226714078927558231944983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-8715573841033074989625983900830000000000000)
      constant := (86374283967381053332629909436702147066914494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree008.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel008

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64123190445156333759/50000000000000000000)
  centralHi := (128246380890312667519/100000000000000000000)
  directionLo := (137101148110075094283/100000000000000000000)
  directionHi := (34275287027518773571/25000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree009.table
  base := (1060610070512762879140568069911629854123/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-147737734367607973401045895929190000000000000)
      constant := (1233748094803069983028619167305608458527148208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree009.table
  base := (1038328801488834918527709455052205132171/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-9567274367310242686943122543510000000000000)
      constant := (78802172931882261683172611473916307460293424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree009.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel009

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137101148110075094283/100000000000000000000)
  centralHi := (34275287027518773571/25000000000000000000)
  directionLo := (145417727305642970039/100000000000000000000)
  directionHi := (3635443182641074251/2500000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree010.table
  base := (1632706642447136818596509250931317589041/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-160866778329276766018179901043710000000000000)
      constant := (1158277221469308769295619851598547068855199368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree010.table
  base := (12739209624534196894705654619531662462149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-10418974893587410384260261186190000000000000)
      constant := (74142097316948987874069833468164439856176541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree010.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel010

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145417727305642970039/100000000000000000000)
  centralHi := (3635443182641074251/2500000000000000000)
  directionLo := (153283743483697365291/100000000000000000000)
  directionHi := (38320935870924341323/25000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree011.table
  base := (2461045109547120057342889568980512674031/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (7353)
      previous := (0)
      next := (4560)
      square := (87897052597500725766577201260000000000000)
      linear := (-1437982002404508749052181042630000000000000)
      constant := (9265103807489203042706967798877860301300764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree011.table
  base := (9555456543412655112566939278864248963007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-11270675419864578081577399828870000000000000)
      constant := (71951373217209856436085982203559675337086663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree011.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel011

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153283743483697365291/100000000000000000000)
  centralHi := (38320935870924341323/25000000000000000000)
  directionLo := (80382673223172803277/50000000000000000000)
  directionHi := (32153069289269121311/20000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree012.table
  base := (1438046899125777309641959274897562407239/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-187124866252614351252447911272750000000000000)
      constant := (1116596884884270034034116360154362117553033795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree012.table
  base := (216682516035032378693183257055802341183/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-12122375946141745778894538471550000000000000)
      constant := (71869996194518893844967494718271960844257504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree012.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel012

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80382673223172803277/50000000000000000000)
  centralHi := (32153069289269121311/20000000000000000000)
  directionLo := (167913928009713123367/100000000000000000000)
  directionHi := (20989241001214140421/12500000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree013.table
  base := (2498120526344438147315315759645158895753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-200253910214283143869581916387270000000000000)
      constant := (1140310966787010740096668036593290371450773586) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree013.table
  base := (1192534474945078353348684428793642694023/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-12974076472418913476211677114230000000000000)
      constant := (73605202061309914667395032900255369310042428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree013.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel013

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167913928009713123367/100000000000000000000)
  centralHi := (20989241001214140421/12500000000000000000)
  directionLo := (87385178693655932303/50000000000000000000)
  directionHi := (174770357387311864607/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree014.table
  base := (3972254027372675762627818537854385581/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-213382954175951936486715921501790000000000000)
      constant := (1188533265972825125105670189291713933250928800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree014.table
  base := (1489796024829471375703969264539638080573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-13825776998696081173528815756910000000000000)
      constant := (76918909377251011114114078748283686736659114) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree014.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel014

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87385178693655932303/50000000000000000000)
  centralHi := (174770357387311864607/100000000000000000000)
  directionLo := (181367771180345898561/100000000000000000000)
  directionHi := (90683885590172949281/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree015.table
  base := (416537739678719041692491280625116502587/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-226511998137620729103849926616310000000000000)
      constant := (1258259838126082677897101615789092855798010988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree015.table
  base := (186659687267373667329366213312766006927/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-14677477524973248870845954399590000000000000)
      constant := (81617506512230404349940049938914477707663544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree015.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel015

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181367771180345898561/100000000000000000000)
  centralHi := (90683885590172949281/50000000000000000000)
  directionLo := (18773347869936225561/10000000000000000000)
  directionHi := (187733478699362255611/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree016.table
  base := (10131194281735988457857769797466906529/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-239641042099289521720983931730830000000000000)
      constant := (1347042953245425503965902350569246077763729960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree016.table
  base := (127571557211871870707420420941084713631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-15529178051250416568163093042270000000000000)
      constant := (87543545839840137575719561502927013921178958) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree016.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel016

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18773347869936225561/10000000000000000000)
  centralHi := (187733478699362255611/100000000000000000000)
  directionLo := (96945151537095313359/50000000000000000000)
  directionHi := (193890303074190626719/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree017.table
  base := (-325283470529061704901581553501871756071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-252770086060958314338117936845350000000000000)
      constant := (1452888110635173386761298143158579479646125298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree017.table
  base := (-390196274588786353077643243655297784581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-16380878577527584265480231684950000000000000)
      constant := (94568989073516813518931203231434537046223942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree017.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel017

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96945151537095313359/50000000000000000000)
  centralHi := (193890303074190626719/100000000000000000000)
  directionLo := (199857549839477139137/100000000000000000000)
  directionHi := (99928774919738569569/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree018.table
  base := (-1538499054410107796579651736549473427613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-265899130022627106955251941959870000000000000)
      constant := (1574170120419554733190372511670802451208436547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree018.table
  base := (-165039680450337282953249060497531522779/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-17232579103804751962797370327630000000000000)
      constant := (102589714134306330552866154472604339525137890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree018.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel018

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199857549839477139137/100000000000000000000)
  centralHi := (99928774919738569569/50000000000000000000)
  directionLo := (12853232635319540089/6250000000000000000)
  directionHi := (8226068886604505657/4000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree019.table
  base := (-2288865191137198660140106498074789284743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22990000000000000000000000000000000000000000
      center := (46827)
      previous := (0)
      next := (29040)
      square := (559765440226188832513465334340000000000000)
      linear := (-14685693367594521030125576161810000000000000)
      constant := (89977090643035224742252076523376059434375843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree019.table
  base := (-119250656730407524762404190221976682063/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-18084279630081919660114508970310000000000000)
      constant := (111521047978308615406437958994479350001700660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree019.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel019

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12853232635319540089/6250000000000000000)
  centralHi := (8226068886604505657/4000000000000000000)
  directionLo := (211287059308217633073/100000000000000000000)
  directionHi := (105643529654108816537/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree020.table
  base := (-2926368342503115473789483931137677881719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-292157217945964692189519952188910000000000000)
      constant := (1857992864668126467185115163374175092448632361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree020.table
  base := (-601750893924914733119343216705022942457/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-18935980156359087357431647612990000000000000)
      constant := (121294133784781003773560944953177952773191435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree020.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel020

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211287059308217633073/100000000000000000000)
  centralHi := (105643529654108816537/50000000000000000000)
  directionLo := (108387974462981672827/50000000000000000000)
  directionHi := (43355189785192669131/20000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree021.table
  base := (-3471137304517291405288093100530070638911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-305286261907633484806653957303430000000000000)
      constant := (2018575301832438274236411579701715984421728609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree021.table
  base := (-708310981072496996167290323986465157309/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-19787680682636255054748786255670000000000000)
      constant := (131852976678593647677750210073540096865595095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree021.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel021

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108387974462981672827/50000000000000000000)
  centralHi := (43355189785192669131/20000000000000000000)
  directionLo := (111064623794425944161/50000000000000000000)
  directionHi := (222129247588851888323/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree022.table
  base := (-1969786827567195140845263110147286657201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (7353)
      previous := (0)
      next := (4560)
      square := (87897052597500725766577201260000000000000)
      linear := (-2631531453465308077882545143950000000000000)
      constant := (18104095837884024963860388929133659033500878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree022.table
  base := (-799924995973694834832866106655705665239/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-20639381208913422752065924898350000000000000)
      constant := (143152041258373676558455268659560613931718245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree022.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel022

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111064623794425944161/50000000000000000000)
  centralHi := (222129247588851888323/100000000000000000000)
  directionLo := (113678266652015608453/50000000000000000000)
  directionHi := (227356533304031216907/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree023.table
  base := (-869008381214627960377743646092724682049/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-331544349830971070040921967532470000000000000)
      constant := (2373469973086326961741902995428988465817088155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree023.table
  base := (-2198073599015529024313476614201471959067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-21491081735190590449383063541030000000000000)
      constant := (155154297867889246715918220174046130533961594) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree023.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel023

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113678266652015608453/50000000000000000000)
  centralHi := (227356533304031216907/100000000000000000000)
  directionLo := (116233153443482562753/50000000000000000000)
  directionHi := (232466306886965125507/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree024.table
  base := (-293651991604800169914866779418697489043/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-344673393792639862658055972646990000000000000)
      constant := (2566722754221276037277699522357389999697803472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree024.table
  base := (-1185460410541148447402148615707601124933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-22342782261467758146700202183710000000000000)
      constant := (167829633795919328816394636823109393760252812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree024.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel024

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116233153443482562753/50000000000000000000)
  centralHi := (232466306886965125507/100000000000000000000)
  directionLo := (5936653857566895549/2500000000000000000)
  directionHi := (237466154302675821961/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree025.table
  base := (-2504308436734361483119294899423028971007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-357802437754308655275189977761510000000000000)
      constant := (2769966343445095060840311570966855343034886466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree025.table
  base := (-2522712966915134424298788678806963404759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-23194482787744925844017340826390000000000000)
      constant := (181153561243498547308653818959712479592063938) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree025.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel025

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5936653857566895549/2500000000000000000)
  centralHi := (237466154302675821961/100000000000000000000)
  directionLo := (121181439421369141699/50000000000000000000)
  directionHi := (242362878842738283399/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree026.table
  base := (-1320706796605968442453020458149624484583/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-370931481715977447892323982876030000000000000)
      constant := (2982884915902860226983220020756885011555719908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree026.table
  base := (-5313989280132640928585698245515723437573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-24046183314022093541334479469070000000000000)
      constant := (195106166627870199604991810685126332863857443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree026.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel026

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121181439421369141699/50000000000000000000)
  centralHi := (242362878842738283399/100000000000000000000)
  directionLo := (61790652429482320167/25000000000000000000)
  directionHi := (247162609717929280669/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree027.table
  base := (-2763477113658309786368052343623742824911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-384060525677646240509457987990550000000000000)
      constant := (3205221128356364522455240932131452579330125218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree027.table
  base := (-5553296652080151550671325425266770426527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-24897883840299261238651618111750000000000000)
      constant := (209671256145471573472643295448215641871885657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree027.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel027

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61790652429482320167/25000000000000000000)
  centralHi := (247162609717929280669/100000000000000000000)
  directionLo := (5037417840291393701/2000000000000000000)
  directionHi := (251870892014569685051/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree028.table
  base := (-359112406044508342308526625718518455123/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-397189569639315033126591993105070000000000000)
      constant := (3436765290140420620991154848427550325788355792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree028.table
  base := (-230721445811339150224846959851848369363/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-25749584366576428935968756754430000000000000)
      constant := (224835660935732274295094570534683948261483325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree028.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel028

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5037417840291393701/2000000000000000000)
  centralHi := (251870892014569685051/100000000000000000000)
  directionLo := (64123190445156333759/25000000000000000000)
  directionHi := (256492761780625335037/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree029.table
  base := (-2971635789955699938191187481998198087677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-410318613600983825743725998219590000000000000)
      constant := (3677346539297496223277987502666123418664361926) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree029.table
  base := (-5962020135748840990035795877300973165373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-26601284892853596633285895397110000000000000)
      constant := (240588672034450834455844685604911566378467243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree029.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel029

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64123190445156333759/25000000000000000000)
  centralHi := (256492761780625335037/100000000000000000000)
  directionLo := (261032809139943575099/100000000000000000000)
  directionHi := (2610328091399435751/1000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree030.table
  base := (-1530640187185773502969720572700770441941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-423447657562652618360860003334110000000000000)
      constant := (3926825652606842966122138714928730585302300716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree030.table
  base := (-6138348861262997524023553211655266304019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-27452985419130764330603034039790000000000000)
      constant := (256921580873684247165159251398160356952010629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree030.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel030

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261032809139943575099/100000000000000000000)
  centralHi := (2610328091399435751/1000000000000000000)
  directionLo := (16593451980507415877/6250000000000000000)
  directionHi := (265495231688118654033/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree031.table
  base := (-6286263084277232914736645153243652031601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-436576701524321410977994008448630000000000000)
      constant := (4185089186970241435578925922511434035607636719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree031.table
  base := (-6299543446840519617271303696917251535399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-28304685945407932027920172682470000000000000)
      constant := (273827305613266581754577884641989440437064209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree031.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel031

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16593451980507415877/6250000000000000000)
  centralHi := (265495231688118654033/100000000000000000000)
  directionLo := (269883879938697703869/100000000000000000000)
  directionHi := (26988387993869770387/10000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree032.table
  base := (-6436494764110887407212305882118744538967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-449705745485990203595128013563150000000000000)
      constant := (4452044705634073981061356731762531119793382473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree032.table
  base := (-805956760220748895910041110736658359061/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-29156386471685099725237311325150000000000000)
      constant := (291300087271497442056019485454565813355181208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree032.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel032

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269883879938697703869/100000000000000000000)
  centralHi := (26988387993869770387/10000000000000000000)
  directionLo := (137101148110075094283/50000000000000000000)
  directionHi := (274202296220150188567/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree033.table
  base := (-6574980112896447138544178654233144458681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (7353)
      previous := (0)
      next := (4560)
      square := (87897052597500725766577201260000000000000)
      linear := (-3825080904526107406712909245270000000000000)
      constant := (39071213953497517109926052405991834850416159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree033.table
  base := (-6584347989680726746901991867287474841667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-30008086997962267422554449967830000000000000)
      constant := (309335242617168375434344574919719483169757397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree033.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel033

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137101148110075094283/50000000000000000000)
  centralHi := (274202296220150188567/100000000000000000000)
  directionLo := (278453748141483245213/100000000000000000000)
  directionHi := (139226874070741622607/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree034.table
  base := (-6703124163286255679267455686815543234517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-475963833409327788829396023792190000000000000)
      constant := (5011744361956331183793465019358110255973062923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree034.table
  base := (-6710980966203662545708463887184276063731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-30859787524239435119871588610510000000000000)
      constant := (327928963220385790133044924007199368536979621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree034.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel034

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278453748141483245213/100000000000000000000)
  centralHi := (139226874070741622607/50000000000000000000)
  directionLo := (282641257525645355467/100000000000000000000)
  directionHi := (70660314381411338867/25000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree035.table
  base := (-6822071780630906547819978028236023171091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-489092877370996581446530028906710000000000000)
      constant := (5304377117520089546059711431627972271863574029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree035.table
  base := (-6828655553548365654279316273872547761457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-31711488050516602817188727253190000000000000)
      constant := (347078152040071776194682516855842013338067287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree035.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel035

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282641257525645355467/100000000000000000000)
  centralHi := (70660314381411338867/25000000000000000000)
  directionLo := (2294141004312553001/800000000000000000)
  directionHi := (143383812769534562563/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree036.table
  base := (-6932755839401304610631351972951895761231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-502221921332665374063664034021230000000000000)
      constant := (5605474406174711061629279945386408241253668689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree036.table
  base := (-1734567087064402884915445304198240348239/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-32563188576793770514505865895870000000000000)
      constant := (366780290536537677332321678245508571447186596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree036.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel036

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2294141004312553001/800000000000000000)
  centralHi := (143383812769534562563/50000000000000000000)
  directionLo := (145417727305642970039/50000000000000000000)
  directionHi := (290835454611285940079/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree037.table
  base := (-1407187295724073112078302497927604015737/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-515350965294334166680798039135750000000000000)
      constant := (5915003024287535750129781511266731644942960515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree037.table
  base := (-3520274235963736191655305957208922174977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-33414889103070938211823004538550000000000000)
      constant := (387033330607220126788256006441690275220979214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree037.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel037

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145417727305642970039/50000000000000000000)
  centralHi := (290835454611285940079/100000000000000000000)
  directionLo := (294847167631963115041/100000000000000000000)
  directionHi := (147423583815981557521/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree038.table
  base := (-891529136025810459090470719289947097111/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22990000000000000000000000000000000000000000
      center := (46827)
      previous := (0)
      next := (29040)
      square := (559765440226188832513465334340000000000000)
      linear := (-27814737329263313647259581276330000000000000)
      constant := (328049258751975696379353394325999292989934488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree038.table
  base := (-713608885563196260253870993476988300429/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-34266589629348105909140143181230000000000000)
      constant := (407835606708732218064253560939811398640949390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree038.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel038

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294847167631963115041/100000000000000000000)
  centralHi := (147423583815981557521/50000000000000000000)
  directionLo := (298805024827609870443/100000000000000000000)
  directionHi := (74701256206902467611/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree039.table
  base := (-3611075186126894347251519764733071372349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-541609053217671751915066049364790000000000000)
      constant := (6559251036195182823389835168575739418768846662) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree039.table
  base := (-7225371680420527824389123750869099942523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-35118290155625273606457281823910000000000000)
      constant := (429185764394506058393950418579158698261452893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree039.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel039

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298805024827609870443/100000000000000000000)
  centralHi := (74701256206902467611/25000000000000000000)
  directionLo := (302711138651794814551/100000000000000000000)
  directionHi := (37838892331474351819/12500000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree040.table
  base := (-1461219917206820787783322955143956379231/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-554738097179340544532200054479310000000000000)
      constant := (6893930419968941012532809920770184206994053445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree040.table
  base := (-3654394532757868280698853672662817432073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-35969990681902441303774420466590000000000000)
      constant := (451082702201645452825633365522580291666613886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree040.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel040

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302711138651794814551/100000000000000000000)
  centralHi := (37838892331474351819/12500000000000000000)
  directionLo := (306567486967394730583/100000000000000000000)
  directionHi := (38320935870924341323/12500000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree041.table
  base := (-7384415840415606511255790450681178566773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-567867141141009337149334059593830000000000000)
      constant := (7236959429630979954500409519010365439024788587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree041.table
  base := (-923332486491234609673819082837763367939/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-36821691208179609001091559109270000000000000)
      constant := (473525524393386884188014909497799781595674792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree041.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel041

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306567486967394730583/100000000000000000000)
  centralHi := (38320935870924341323/12500000000000000000)
  directionLo := (310375924754387693527/100000000000000000000)
  directionHi := (38796990594298461691/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree042.table
  base := (-1864343050477084280381296503421279880107/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-580996185102678129766468064708350000000000000)
      constant := (7588326137363074561038922180693080294228184532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree042.table
  base := (-7459243483398490519924881688932562852113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-37673391734456776698408697751950000000000000)
      constant := (496513502529357215712206813946328430948414583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree042.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel042

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310375924754387693527/100000000000000000000)
  centralHi := (38796990594298461691/12500000000000000000)
  directionLo := (62827638907977092589/20000000000000000000)
  directionHi := (157069097269942731473/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree043.table
  base := (-3762595590851971078312421083397355495787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-594125229064346922383602069822870000000000000)
      constant := (7948020823653862526322167227911510229177056106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree043.table
  base := (-7526750731681913617088587464745290637207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-38525092260733944395725836394630000000000000)
      constant := (520046044214601663214410187316760478600085537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree043.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel043

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62827638907977092589/20000000000000000000)
  centralHi := (157069097269942731473/50000000000000000000)
  directionLo := (19865995982301378809/6250000000000000000)
  directionHi := (63571187143364412189/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree044.table
  base := (-1517610819440523972626203570901426695729/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (7353)
      previous := (0)
      next := (4560)
      square := (87897052597500725766577201260000000000000)
      linear := (-5018630355586906735543273346590000000000000)
      constant := (68727566680809799923483033832322924814209155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree044.table
  base := (-7589353143627168034133564724287958294017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-39376792787011112093042975037310000000000000)
      constant := (544122667686386942275132457300875125152106247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree044.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel044

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19865995982301378809/6250000000000000000)
  centralHi := (63571187143364412189/20000000000000000000)
  directionLo := (321530692892691213109/100000000000000000000)
  directionHi := (32153069289269121311/10000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree045.table
  base := (-1911527174997745745648147104972582566527/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-620383316987684507617870080051910000000000000)
      constant := (8692363917598389523133165354231220483646136452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree045.table
  base := (-7647190198207215242629066863103026889479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-40228493313288279790360113679990000000000000)
      constant := (568742981148278004120735591110593597467453489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree045.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel045

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321530692892691213109/100000000000000000000)
  centralHi := (32153069289269121311/10000000000000000000)
  directionLo := (162581961694472509241/50000000000000000000)
  directionHi := (325163923388945018483/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree046.table
  base := (-7699475391283263326602163510521680609803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-633512360949353300235004085166430000000000000)
      constant := (9077000612069634863735145227456122469283195157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree046.table
  base := (-7700375329236586019954074777407909632053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-41080193839565447487677252322670000000000000)
      constant := (593906665964689831797562031408441181843563123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree046.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel046

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (162581961694472509241/50000000000000000000)
  centralHi := (325163923388945018483/100000000000000000000)
  directionLo := (2630056031954656877/800000000000000000)
  directionHi := (164378501997166054813/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree047.table
  base := (-3874126143197659574602139280389448207651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-646641404911022092852138090280950000000000000)
      constant := (9469941366016609808152467361076727025683193338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree047.table
  base := (-3874500395245161657068517730560194285771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-41931894365842615184994390965350000000000000)
      constant := (619613462994768329664599870588502828502538522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree047.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel047

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2630056031954656877/800000000000000000)
  centralHi := (164378501997166054813/50000000000000000000)
  directionLo := (332311237060931919567/100000000000000000000)
  directionHi := (20769452316308244973/6250000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree048.table
  base := (-7792519341384990918409127444133974397517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-659770448872690885469272095395470000000000000)
      constant := (9871182686878751826901978476505903864342059923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree048.table
  base := (-7793141611996776986202740996921025247017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-42783594892119782882311529608030000000000000)
      constant := (645863161479163862962230467690528840081129247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree048.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel048

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (332311237060931919567/100000000000000000000)
  centralHi := (20769452316308244973/6250000000000000000)
  directionLo := (167913928009713123367/50000000000000000000)
  directionHi := (67165571203885249347/20000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree049.table
  base := (-1566468343105070288631188272548705483403/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-672899492834359678086406100509990000000000000)
      constant := (10280721728433853826616404015602249978897367785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree049.table
  base := (-979107352159554726064141240947883477991/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-43635295418396950579628668250710000000000000)
      constant := (672655590002807373110889137347869162482586248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree049.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel049

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167913928009713123367/50000000000000000000)
  centralHi := (67165571203885249347/20000000000000000000)
  directionLo := (339308030379833596757/100000000000000000000)
  directionHi := (169654015189916798379/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree050.table
  base := (-7867772511118564112215397223723683165127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-686028536796028470703540105624510000000000000)
      constant := (10698556171120255008310852040386025795664087513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree050.table
  base := (-983525254948175375259637585348946962947/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-44486995944674118276945806893390000000000000)
      constant := (699990609145882483016761883871538463848655016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree050.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel050

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (339308030379833596757/100000000000000000000)
  centralHi := (169654015189916798379/50000000000000000000)
  directionLo := (85688217568796933927/25000000000000000000)
  directionHi := (342752870275187735709/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree051.table
  base := (-7898855005954159649488989482019089308567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-699157580757697263320674110739030000000000000)
      constant := (11124684124520830880434581371570794159912484873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree051.table
  base := (-789921164943248661764930353613264646673/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-45338696470951285974262945536070000000000000)
      constant := (727868105507629934011278894643033396074955430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree051.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel051

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85688217568796933927/25000000000000000000)
  centralHi := (342752870275187735709/100000000000000000000)
  directionLo := (5408803603096930021/1562500000000000000)
  directionHi := (69232686119640704269/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree052.table
  base := (-7925624472363900023376428508493227089349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-712286624719366055937808115853550000000000000)
      constant := (11559104047904857748445924260446867347510146331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree052.table
  base := (-7925920484666856429041036120550360843899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-46190396997228453671580084178750000000000000)
      constant := (756287986846531413817804234611414036389487709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree052.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel052

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5408803603096930021/1562500000000000000)
  centralHi := (69232686119640704269/20000000000000000000)
  directionLo := (87385178693655932303/25000000000000000000)
  directionHi := (349540714774623729213/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree053.table
  base := (-1987027414856881548774499416231141258573/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-725415668681034848554942120968070000000000000)
      constant := (12001814685483783447417817509488400074737091148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree053.table
  base := (-7948355257378521840585536422630281122663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (1089)
      previous := (0)
      next := (660)
      square := (12904553428441934807835433980000000000000)
      linear := (-887586745726521157903721185310000000000000)
      constant := (14816041096760869547538978080610595100498861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree053.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel053

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87385178693655932303/25000000000000000000)
  centralHi := (349540714774623729213/100000000000000000000)
  directionLo := (352885678211503013711/100000000000000000000)
  directionHi := (22055354888218938357/6250000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree054.table
  base := (-7966334000707462595372569418891333477259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-738544712642703641172076126082590000000000000)
      constant := (12452815013656167715792030050439107662379849621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree054.table
  base := (-995817212248153715242228317141443147547/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-47893798049782789066214361464110000000000000)
      constant := (814754618312270499659702748561697489588323816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree054.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel054

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352885678211503013711/100000000000000000000)
  centralHi := (22055354888218938357/6250000000000000000)
  directionLo := (17809961572700686647/5000000000000000000)
  directionHi := (356199231454013732941/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree055.table
  base := (-3990158299169709296574964627181805041403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (7353)
      previous := (0)
      next := (4560)
      square := (87897052597500725766577201260000000000000)
      linear := (-6212179806647706064373637447910000000000000)
      constant := (106711604942327443244822035566724736760107034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree055.table
  base := (-498780342850078344177072705920257752609/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-48745498576059956763531500106790000000000000)
      constant := (844801257737732660662852629042069935566741104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree055.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel055

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17809961572700686647/5000000000000000000)
  centralHi := (356199231454013732941/100000000000000000000)
  directionLo := (22467640192520813949/6250000000000000000)
  directionHi := (71896448616066604637/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree056.table
  base := (-1997518256223422969396333102768721354397/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-764802800566041226406344136311630000000000000)
      constant := (13379681558354699024552135564765357930074338572) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree056.table
  base := (-1598042600922450160316029709752551508843/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-49597199102337124460848638749470000000000000)
      constant := (875390055998973256812894617107405414058300065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree056.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel056

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22467640192520813949/6250000000000000000)
  centralHi := (71896448616066604637/20000000000000000000)
  directionLo := (362735542360691797123/100000000000000000000)
  directionHi := (90683885590172949281/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree057.table
  base := (-7995615976752756044164193916433658407711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22990000000000000000000000000000000000000000
      center := (46827)
      previous := (0)
      next := (29040)
      square := (559765440226188832513465334340000000000000)
      linear := (-40943781290932106264393586390850000000000000)
      constant := (729239291582353687497559969484309019320672411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree057.table
  base := (-7995731959922277393405571115492266436467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-50448899628614292158165777392150000000000000)
      constant := (906520980216916795403508662972872223579964197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree057.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel057

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (362735542360691797123/100000000000000000000)
  centralHi := (90683885590172949281/25000000000000000000)
  directionLo := (2859061888309778309/781250000000000000)
  directionHi := (365959921703651623553/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree058.table
  base := (-1999238951625415735253047264639511646053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-791060888489378811640612146540670000000000000)
      constant := (14339698690940416096550000247622945967155035628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree058.table
  base := (-3998525938637076478403173039655649734761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-51300600154891459855482916034830000000000000)
      constant := (938194003633751695969032932166394559790112702) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree058.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel058

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2859061888309778309/781250000000000000)
  centralHi := (365959921703651623553/100000000000000000000)
  directionLo := (73831227782011161697/20000000000000000000)
  directionHi := (184578069455027904243/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree059.table
  base := (-7994100956735929864671139520060352007309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-804189932451047604257746151655190000000000000)
      constant := (14832137642200772335810974734110393763968735571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree059.table
  base := (-7994180510112427617663051331577347859489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-52152300681168627552800054677510000000000000)
      constant := (970409104470052217205868881391149229862695399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree059.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel059

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73831227782011161697/20000000000000000000)
  centralHi := (184578069455027904243/50000000000000000000)
  directionLo := (74464983850563753017/20000000000000000000)
  directionHi := (186162459626409382543/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree060.table
  base := (-3993529156771314548475826293813678588293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-817318976412716396874880156769710000000000000)
      constant := (15332863093054619375894793742774449411169546934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree060.table
  base := (-7987124170447563874985193463784960891363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-53004001207445795250117193320190000000000000)
      constant := (1003166264995380969954298806631628044856161333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree060.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel060

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74464983850563753017/20000000000000000000)
  centralHi := (186162459626409382543/50000000000000000000)
  directionLo := (18773347869936225561/5000000000000000000)
  directionHi := (375466957398724511221/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree061.table
  base := (-7975833494529748418296367662169108137201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-830448020374385189492014161884230000000000000)
      constant := (15841874798119222702563942341943961187458923119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree061.table
  base := (-159517759958370459289432537299973388719/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-53855701733722962947434331962870000000000000)
      constant := (1036465470772492112103244625908948737554416450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree061.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel061

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18773347869936225561/5000000000000000000)
  centralHi := (375466957398724511221/100000000000000000000)
  directionLo := (378582919186660084619/100000000000000000000)
  directionHi := (18929145959333004231/5000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree062.table
  base := (-995053885440534239836647476227914055247/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-843577064336053982109148166998750000000000000)
      constant := (16359172557168435736421659287234967889222046344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree062.table
  base := (-3980238089299387319799946487418303432109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-54707402260000130644751470605550000000000000)
      constant := (1070306710042705267115187925319223971318411638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree062.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel062

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (378582919186660084619/100000000000000000000)
  centralHi := (18929145959333004231/5000000000000000000)
  directionLo := (190836721637589180393/50000000000000000000)
  directionHi := (381673443275178360787/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree063.table
  base := (-7940854821814933506957356245776297066981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-856706108297722774726282172113270000000000000)
      constant := (16884756206779025553682984891420915567817202939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree063.table
  base := (-7940892122934023797286805879665614308861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-55559102786277298342068609248230000000000000)
      constant := (1104689973226078449934689374093849289406409451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree063.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel063

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190836721637589180393/50000000000000000000)
  centralHi := (381673443275178360787/100000000000000000000)
  directionLo := (192369571335469001277/50000000000000000000)
  directionHi := (76947828534187600511/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree064.table
  base := (-3958553881993335292251376284181536376927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-869835152259391567343416177227790000000000000)
      constant := (17418625613523667241630760528110932619038903426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree064.table
  base := (-3958569305223057708128347379530328430189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-56410803312554466039385747890910000000000000)
      constant := (1139615252514934798016512331567398614879198198) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree064.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel064

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (192369571335469001277/50000000000000000000)
  centralHi := (76947828534187600511/20000000000000000000)
  directionLo := (387780606148381253437/100000000000000000000)
  directionHi := (193890303074190626719/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree065.table
  base := (-394459620245186185851643799838135648707/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-882964196221060359960550182342310000000000000)
      constant := (17960780668424195995476491298464057934576590660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree065.table
  base := (-7889217907411378480252737459914186835027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-57262503838831633736702886533590000000000000)
      constant := (1175082541543304103245322211167951049180409157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree065.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel065

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387780606148381253437/100000000000000000000)
  centralHi := (193890303074190626719/50000000000000000000)
  directionLo := (195399199784980935209/50000000000000000000)
  directionHi := (390798399569961870419/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree066.table
  base := (-3928555391591976938376015608597131107957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (7353)
      previous := (0)
      next := (4560)
      square := (87897052597500725766577201260000000000000)
      linear := (-7405729257708505393204001549230000000000000)
      constant := (152985299854807810166060503880012871340055046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree066.table
  base := (-1964282965640474150442377776999074058119/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-58114204365108801434020025176270000000000000)
      constant := (1211091835118097942753621745749218403882974916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree066.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel066

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195399199784980935209/50000000000000000000)
  centralHi := (390798399569961870419/100000000000000000000)
  directionLo := (24612066694706725933/6250000000000000000)
  directionHi := (393793067115307614929/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree067.table
  base := (-977608070689710443025869138055126317083/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-909222284144397945194818192571350000000000000)
      constant := (19069947382743614369208487615098022218747979816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree067.table
  base := (-3910440992457538760828757364061090422803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-58965904891385969131337163818950000000000000)
      constant := (1247643129000486418197361883550494794004692746) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree067.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel067

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24612066694706725933/6250000000000000000)
  centralHi := (393793067115307614929/100000000000000000000)
  directionLo := (396765132426878913521/100000000000000000000)
  directionHi := (198382566213439456761/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree068.table
  base := (-486278444711134517316398043713067680987/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-922351328106066737811952197685870000000000000)
      constant := (19636958909801929435703638293439631850028909648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree068.table
  base := (-7780469507069962366880043795034876484147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-59817605417663136828654302461630000000000000)
      constant := (1284736419728098823050902727583227031956031077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree068.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel068

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396765132426878913521/100000000000000000000)
  centralHi := (198382566213439456761/50000000000000000000)
  directionLo := (199857549839477139137/50000000000000000000)
  directionHi := (15988603987158171131/4000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree069.table
  base := (-7735883549013822609955726572095773976271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-935480372067735530429086202800390000000000000)
      constant := (20212255814847841137603274613520334496942506449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree069.table
  base := (-3867947718342527934969977051552549984793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-60669305943940304525971441104310000000000000)
      constant := (1322371704470422417520643755921027774185432926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree069.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel069

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199857549839477139137/50000000000000000000)
  centralHi := (15988603987158171131/4000000000000000000)
  directionLo := (196603249304747269/48828125000000000)
  directionHi := (402643454576122406913/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree070.table
  base := (-7687150781077542563946302493596069015399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-948609416029404323046220207914910000000000000)
      constant := (20795838057928398420499506350382930109338356281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree070.table
  base := (-7687160598345306284389393085279679376081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-61521006470217472223288579746990000000000000)
      constant := (1360548980911198081962356986424749380632588471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree070.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel070

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196603249304747269/48828125000000000)
  centralHi := (402643454576122406913/100000000000000000000)
  directionLo := (405550665286880698853/100000000000000000000)
  directionHi := (202775332643440349427/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree071.table
  base := (-238570548806608133731259477830997634831/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-961738459991073115663354213029430000000000000)
      constant := (21387705606272274011472997223631124154014306848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree071.table
  base := (-7634265667613453801091246319446542928329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-62372706996494639920605718389670000000000000)
      constant := (1399268247152770079179908573506104660914323839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree071.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel071

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405550665286880698853/100000000000000000000)
  centralHi := (202775332643440349427/50000000000000000000)
  directionLo := (408437183317421694957/100000000000000000000)
  directionHi := (204218591658710847479/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree072.table
  base := (-7577204507351237449320214512284124189871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (10635543364297587817755841352460000000000000)
      linear := (-974867503952741908280488218143950000000000000)
      constant := (21987858432966046072111705661990277171262244849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree072.table
  base := (-3788605599362799992461780744773557037687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (57717)
      previous := (0)
      next := (34980)
      square := (683941331707422544815278000940000000000000)
      linear := (-63224407522771807617922857032350000000000000)
      constant := (1438529501638289199877556081220902156562274434) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree072.checked
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
end ForestUnimodality.Stage170KernelData.Cell547.Kernel072

namespace ForestUnimodality.Stage170KernelData.Cell547
open FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem degreePropagationThreshold : row.degreePropagationCheck 72 interval.lo interval.hi = true := by
  decide +kernel

theorem degreePropagationTail (n : ℕ) (hn : 72 ≤ n) (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual n j q :=
  row.degreePropagationCheck_sound 72 interval.lo interval.hi degreePropagationThreshold
    (fun _q hq j => Kernel072.actual_residual_nonneg j hq) n hn q hq j
end ForestUnimodality.Stage170KernelData.Cell547

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel073
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  degreePropagationTail 73 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel073

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel074
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  degreePropagationTail 74 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel074

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel075
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  degreePropagationTail 75 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel075

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel076
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  degreePropagationTail 76 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel076

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel077
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  degreePropagationTail 77 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel077

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel078
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  degreePropagationTail 78 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel078

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel079
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  degreePropagationTail 79 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel079

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel080
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  degreePropagationTail 80 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel080

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel081
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  degreePropagationTail 81 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel081

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel082
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  degreePropagationTail 82 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel082

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel083
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  degreePropagationTail 83 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel083

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel084
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  degreePropagationTail 84 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel084

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel085
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  degreePropagationTail 85 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel085

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel086
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  degreePropagationTail 86 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel086

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel087
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  degreePropagationTail 87 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel087

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel088
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  degreePropagationTail 88 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel088

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel089
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  degreePropagationTail 89 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel089

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel090
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  degreePropagationTail 90 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel090

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel091
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  degreePropagationTail 91 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel091

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel092
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  degreePropagationTail 92 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel092

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel093
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  degreePropagationTail 93 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel093

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel094
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  degreePropagationTail 94 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel094

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel095
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  degreePropagationTail 95 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel095

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel096
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  degreePropagationTail 96 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel096

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel097
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  degreePropagationTail 97 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel097

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel098
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  degreePropagationTail 98 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel098

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel099
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  degreePropagationTail 99 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel099

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel100
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  degreePropagationTail 100 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel100

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel101
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  degreePropagationTail 101 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel101

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel102
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  degreePropagationTail 102 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel102

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel103
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  degreePropagationTail 103 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel103

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel104
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  degreePropagationTail 104 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel104

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel105
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  degreePropagationTail 105 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel105

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel106
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  degreePropagationTail 106 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel106

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel107
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  degreePropagationTail 107 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel107

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel108
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  degreePropagationTail 108 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel108

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel109
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  degreePropagationTail 109 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel109

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel110
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  degreePropagationTail 110 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel110

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel111
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  degreePropagationTail 111 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel111

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel112
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  degreePropagationTail 112 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel112

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel113
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  degreePropagationTail 113 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel113

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel114
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  degreePropagationTail 114 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel114

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel115
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  degreePropagationTail 115 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel115

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel116
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  degreePropagationTail 116 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel116

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel117
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  degreePropagationTail 117 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel117

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel118
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  degreePropagationTail 118 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel118

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel119
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  degreePropagationTail 119 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel119

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel120
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  degreePropagationTail 120 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel120

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel121
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  degreePropagationTail 121 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel121

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel122
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  degreePropagationTail 122 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel122

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel123
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  degreePropagationTail 123 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel123

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel124
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  degreePropagationTail 124 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel124

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel125
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  degreePropagationTail 125 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel125

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel126
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  degreePropagationTail 126 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel126

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel127
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  degreePropagationTail 127 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel127

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel128
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  degreePropagationTail 128 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel128

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel129
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  degreePropagationTail 129 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel129

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel130
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  degreePropagationTail 130 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel130

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel131
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  degreePropagationTail 131 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel131

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel132
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  degreePropagationTail 132 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel132

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel133
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  degreePropagationTail 133 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel133

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel134
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  degreePropagationTail 134 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel134

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel135
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  degreePropagationTail 135 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel135

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel136
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  degreePropagationTail 136 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel136

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel137
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  degreePropagationTail 137 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel137

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel138
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  degreePropagationTail 138 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel138

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel139
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  degreePropagationTail 139 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel139

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel140
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  degreePropagationTail 140 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel140

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel141
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  degreePropagationTail 141 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel141

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel142
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  degreePropagationTail 142 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel142

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel143
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  degreePropagationTail 143 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel143

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel144
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  degreePropagationTail 144 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel144

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel145
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  degreePropagationTail 145 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel145

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel146
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  degreePropagationTail 146 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel146

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel147
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  degreePropagationTail 147 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel147

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel148
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  degreePropagationTail 148 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel148

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel149
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  degreePropagationTail 149 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel149

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel150
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  degreePropagationTail 150 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel150

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel151
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  degreePropagationTail 151 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel151

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel152
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  degreePropagationTail 152 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel152

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel153
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  degreePropagationTail 153 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel153

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel154
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  degreePropagationTail 154 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel154

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel155
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  degreePropagationTail 155 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel155

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel156
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  degreePropagationTail 156 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel156

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel157
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  degreePropagationTail 157 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel157

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel158
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  degreePropagationTail 158 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel158

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel159
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  degreePropagationTail 159 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel159

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel160
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  degreePropagationTail 160 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel160

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel161
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  degreePropagationTail 161 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel161

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel162
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  degreePropagationTail 162 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel162

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel163
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  degreePropagationTail 163 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel163

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel164
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  degreePropagationTail 164 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel164

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel165
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  degreePropagationTail 165 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel165

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel166
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  degreePropagationTail 166 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel166

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel167
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  degreePropagationTail 167 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel167

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel168
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  degreePropagationTail 168 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel168

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel169
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  degreePropagationTail 169 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel169

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel170
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 170 j q :=
  degreePropagationTail 170 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel170

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel171
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 171 j q :=
  degreePropagationTail 171 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel171

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel172
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 172 j q :=
  degreePropagationTail 172 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel172

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel173
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 173 j q :=
  degreePropagationTail 173 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel173

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel174
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 174 j q :=
  degreePropagationTail 174 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel174

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel175
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 175 j q :=
  degreePropagationTail 175 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel175

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel176
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 176 j q :=
  degreePropagationTail 176 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel176

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel177
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 177 j q :=
  degreePropagationTail 177 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel177

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel178
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 178 j q :=
  degreePropagationTail 178 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel178

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel179
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 179 j q :=
  degreePropagationTail 179 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel179

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel180
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 180 j q :=
  degreePropagationTail 180 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel180

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel181
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 181 j q :=
  degreePropagationTail 181 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel181

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel182
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 182 j q :=
  degreePropagationTail 182 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel182

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel183
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 183 j q :=
  degreePropagationTail 183 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel183

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel184
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 184 j q :=
  degreePropagationTail 184 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel184

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel185
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 185 j q :=
  degreePropagationTail 185 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel185

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel186
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 186 j q :=
  degreePropagationTail 186 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel186

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel187
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 187 j q :=
  degreePropagationTail 187 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel187

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel188
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 188 j q :=
  degreePropagationTail 188 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel188

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel189
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 189 j q :=
  degreePropagationTail 189 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel189

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel190
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 190 j q :=
  degreePropagationTail 190 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel190

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel191
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 191 j q :=
  degreePropagationTail 191 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel191

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel192
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 192 j q :=
  degreePropagationTail 192 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel192

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel193
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 193 j q :=
  degreePropagationTail 193 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel193

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel194
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 194 j q :=
  degreePropagationTail 194 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel194

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel195
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 195 j q :=
  degreePropagationTail 195 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel195

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel196
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 196 j q :=
  degreePropagationTail 196 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel196

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel197
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 197 j q :=
  degreePropagationTail 197 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel197

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel198
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 198 j q :=
  degreePropagationTail 198 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel198

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel199
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 199 j q :=
  degreePropagationTail 199 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel199

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel200
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 200 j q :=
  degreePropagationTail 200 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel200

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel201
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 201 j q :=
  degreePropagationTail 201 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel201

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel202
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 202 j q :=
  degreePropagationTail 202 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel202

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel203
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 203 j q :=
  degreePropagationTail 203 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel203

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel204
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 204 j q :=
  degreePropagationTail 204 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel204

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel205
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 205 j q :=
  degreePropagationTail 205 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel205

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel206
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 206 j q :=
  degreePropagationTail 206 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel206

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel207
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 207 j q :=
  degreePropagationTail 207 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel207

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel208
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 208 j q :=
  degreePropagationTail 208 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel208

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel209
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 209 j q :=
  degreePropagationTail 209 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel209

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel210
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 210 j q :=
  degreePropagationTail 210 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel210

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel211
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 211 j q :=
  degreePropagationTail 211 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel211

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel212
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 212 j q :=
  degreePropagationTail 212 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel212

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel213
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 213 j q :=
  degreePropagationTail 213 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel213

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel214
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 214 j q :=
  degreePropagationTail 214 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel214

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel215
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 215 j q :=
  degreePropagationTail 215 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel215

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel216
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 216 j q :=
  degreePropagationTail 216 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel216

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel217
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 217 j q :=
  degreePropagationTail 217 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel217

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel218
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 218 j q :=
  degreePropagationTail 218 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel218

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel219
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 219 j q :=
  degreePropagationTail 219 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel219

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel220
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 220 j q :=
  degreePropagationTail 220 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel220

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel221
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 221 j q :=
  degreePropagationTail 221 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel221

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel222
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 222 j q :=
  degreePropagationTail 222 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel222

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel223
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 223 j q :=
  degreePropagationTail 223 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel223

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel224
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 224 j q :=
  degreePropagationTail 224 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel224

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel225
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 225 j q :=
  degreePropagationTail 225 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel225

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel226
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 226 j q :=
  degreePropagationTail 226 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel226

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel227
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 227 j q :=
  degreePropagationTail 227 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel227

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel228
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 228 j q :=
  degreePropagationTail 228 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel228

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel229
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 229 j q :=
  degreePropagationTail 229 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel229

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel230
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 230 j q :=
  degreePropagationTail 230 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel230

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel231
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 231 j q :=
  degreePropagationTail 231 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel231

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel232
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 232 j q :=
  degreePropagationTail 232 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel232

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel233
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 233 j q :=
  degreePropagationTail 233 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel233

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel234
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 234 j q :=
  degreePropagationTail 234 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel234

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel235
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 235 j q :=
  degreePropagationTail 235 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel235

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel236
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 236 j q :=
  degreePropagationTail 236 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel236

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel237
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 237 j q :=
  degreePropagationTail 237 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel237

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel238
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 238 j q :=
  degreePropagationTail 238 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel238

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel239
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 239 j q :=
  degreePropagationTail 239 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel239

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel240
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 240 j q :=
  degreePropagationTail 240 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel240

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel241
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 241 j q :=
  degreePropagationTail 241 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel241

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel242
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 242 j q :=
  degreePropagationTail 242 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel242

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel243
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 243 j q :=
  degreePropagationTail 243 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel243

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel244
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 244 j q :=
  degreePropagationTail 244 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel244

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel245
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 245 j q :=
  degreePropagationTail 245 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel245

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel246
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 246 j q :=
  degreePropagationTail 246 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel246

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel247
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 247 j q :=
  degreePropagationTail 247 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel247

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel248
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 248 j q :=
  degreePropagationTail 248 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel248

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel249
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 249 j q :=
  degreePropagationTail 249 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel249

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel250
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 250 j q :=
  degreePropagationTail 250 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel250

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel251
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 251 j q :=
  degreePropagationTail 251 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel251

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel252
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 252 j q :=
  degreePropagationTail 252 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel252

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel253
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 253 j q :=
  degreePropagationTail 253 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel253

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel254
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 254 j q :=
  degreePropagationTail 254 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel254

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel255
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 255 j q :=
  degreePropagationTail 255 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel255

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel256
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 256 j q :=
  degreePropagationTail 256 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel256

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel257
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 257 j q :=
  degreePropagationTail 257 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel257

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel258
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 258 j q :=
  degreePropagationTail 258 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel258

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel259
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 259 j q :=
  degreePropagationTail 259 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel259

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel260
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 260 j q :=
  degreePropagationTail 260 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel260

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel261
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 261 j q :=
  degreePropagationTail 261 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel261

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel262
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 262 j q :=
  degreePropagationTail 262 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel262

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel263
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 263 j q :=
  degreePropagationTail 263 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel263

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel264
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 264 j q :=
  degreePropagationTail 264 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel264

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel265
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 265 j q :=
  degreePropagationTail 265 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel265

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel266
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 266 j q :=
  degreePropagationTail 266 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel266

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel267
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 267 j q :=
  degreePropagationTail 267 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel267

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel268
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 268 j q :=
  degreePropagationTail 268 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel268

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel269
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 269 j q :=
  degreePropagationTail 269 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel269

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel270
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 270 j q :=
  degreePropagationTail 270 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel270

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel271
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 271 j q :=
  degreePropagationTail 271 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel271

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel272
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 272 j q :=
  degreePropagationTail 272 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel272

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel273
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 273 j q :=
  degreePropagationTail 273 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel273

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel274
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 274 j q :=
  degreePropagationTail 274 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel274

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel275
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 275 j q :=
  degreePropagationTail 275 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel275

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel276
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 276 j q :=
  degreePropagationTail 276 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel276

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel277
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 277 j q :=
  degreePropagationTail 277 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel277

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel278
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 278 j q :=
  degreePropagationTail 278 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel278

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel279
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 279 j q :=
  degreePropagationTail 279 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel279

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel280
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 280 j q :=
  degreePropagationTail 280 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel280

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel281
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 281 j q :=
  degreePropagationTail 281 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel281

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel282
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 282 j q :=
  degreePropagationTail 282 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel282

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel283
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 283 j q :=
  degreePropagationTail 283 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel283

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel284
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 284 j q :=
  degreePropagationTail 284 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel284

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel285
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 285 j q :=
  degreePropagationTail 285 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel285

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel286
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 286 j q :=
  degreePropagationTail 286 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel286

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel287
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 287 j q :=
  degreePropagationTail 287 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel287

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel288
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 288 j q :=
  degreePropagationTail 288 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel288

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel289
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 289 j q :=
  degreePropagationTail 289 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel289

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel290
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 290 j q :=
  degreePropagationTail 290 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel290

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel291
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 291 j q :=
  degreePropagationTail 291 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel291

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel292
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 292 j q :=
  degreePropagationTail 292 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel292

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel293
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 293 j q :=
  degreePropagationTail 293 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel293

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel294
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 294 j q :=
  degreePropagationTail 294 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel294

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel295
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 295 j q :=
  degreePropagationTail 295 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel295

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel296
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 296 j q :=
  degreePropagationTail 296 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel296

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel297
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 297 j q :=
  degreePropagationTail 297 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel297

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel298
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 298 j q :=
  degreePropagationTail 298 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel298

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel299
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 299 j q :=
  degreePropagationTail 299 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel299

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel300
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 300 j q :=
  degreePropagationTail 300 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel300

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel301
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 301 j q :=
  degreePropagationTail 301 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel301

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel302
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 302 j q :=
  degreePropagationTail 302 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel302

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel303
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 303 j q :=
  degreePropagationTail 303 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel303

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel304
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 304 j q :=
  degreePropagationTail 304 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel304

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel305
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 305 j q :=
  degreePropagationTail 305 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel305

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel306
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 306 j q :=
  degreePropagationTail 306 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel306

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel307
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 307 j q :=
  degreePropagationTail 307 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel307

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel308
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 308 j q :=
  degreePropagationTail 308 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel308

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel309
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 309 j q :=
  degreePropagationTail 309 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel309

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel310
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 310 j q :=
  degreePropagationTail 310 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel310

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel311
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 311 j q :=
  degreePropagationTail 311 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel311

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel312
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 312 j q :=
  degreePropagationTail 312 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel312

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel313
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 313 j q :=
  degreePropagationTail 313 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel313

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel314
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 314 j q :=
  degreePropagationTail 314 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel314

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel315
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 315 j q :=
  degreePropagationTail 315 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel315

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel316
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 316 j q :=
  degreePropagationTail 316 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel316

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel317
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 317 j q :=
  degreePropagationTail 317 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel317

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel318
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 318 j q :=
  degreePropagationTail 318 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel318

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel319
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 319 j q :=
  degreePropagationTail 319 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel319

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel320
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 320 j q :=
  degreePropagationTail 320 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel320

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel321
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 321 j q :=
  degreePropagationTail 321 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel321

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel322
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 322 j q :=
  degreePropagationTail 322 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel322

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel323
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 323 j q :=
  degreePropagationTail 323 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel323

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel324
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 324 j q :=
  degreePropagationTail 324 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel324

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel325
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 325 j q :=
  degreePropagationTail 325 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel325

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel326
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 326 j q :=
  degreePropagationTail 326 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel326

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel327
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 327 j q :=
  degreePropagationTail 327 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel327

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel328
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 328 j q :=
  degreePropagationTail 328 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel328

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel329
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 329 j q :=
  degreePropagationTail 329 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel329

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel330
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 330 j q :=
  degreePropagationTail 330 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel330

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel331
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 331 j q :=
  degreePropagationTail 331 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel331

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel332
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 332 j q :=
  degreePropagationTail 332 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel332

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel333
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 333 j q :=
  degreePropagationTail 333 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel333

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel334
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 334 j q :=
  degreePropagationTail 334 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel334

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel335
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 335 j q :=
  degreePropagationTail 335 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel335

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel336
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 336 j q :=
  degreePropagationTail 336 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel336

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel337
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 337 j q :=
  degreePropagationTail 337 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel337

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel338
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 338 j q :=
  degreePropagationTail 338 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel338

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel339
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 339 j q :=
  degreePropagationTail 339 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel339

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel340
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 340 j q :=
  degreePropagationTail 340 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel340

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel341
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 341 j q :=
  degreePropagationTail 341 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel341

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel342
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 342 j q :=
  degreePropagationTail 342 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel342

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel343
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 343 j q :=
  degreePropagationTail 343 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel343

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel344
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 344 j q :=
  degreePropagationTail 344 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel344

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel345
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 345 j q :=
  degreePropagationTail 345 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel345

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel346
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 346 j q :=
  degreePropagationTail 346 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel346

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel347
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 347 j q :=
  degreePropagationTail 347 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel347

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel348
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 348 j q :=
  degreePropagationTail 348 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel348

namespace ForestUnimodality.Stage170KernelData.Cell547.Kernel349
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 72 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 349 j q :=
  degreePropagationTail 349 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell547.Kernel349

