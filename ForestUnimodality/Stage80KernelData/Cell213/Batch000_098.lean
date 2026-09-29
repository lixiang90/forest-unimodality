import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell213.Parameters
import ForestUnimodality.BinomialMassData.Q53_93.Batch000_049
import ForestUnimodality.BinomialMassData.Q53_93.Batch050_099
import ForestUnimodality.BinomialMassData.Q107_187.Batch000_049
import ForestUnimodality.BinomialMassData.Q107_187.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel000
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
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree000.table
  base := (92786925337359560056427201/5000000000000000000000000)
  polynomial :=
    { denominator := 232500000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (440)
      square := (19909019106317454063381777802500000000000)
      linear := (-65501277706461215194488899550000000000000)
      constant := (4314592028187219542623864846500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree000.table
  base := (92786925337359560056427201/5000000000000000000000000)
  polynomial :=
    { denominator := 42500000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (80)
      square := (3639283062445126011585916372500000000000)
      linear := (-11973351838815490949530228950000000000000)
      constant := (788688865367556260479631208500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel001
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
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree001.table
  base := (120828754818101702392300205475456524856673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-10935966469294057525074581473620000000000000)
      constant := (353779841108111122809297911019851161161788259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree001.table
  base := (120573188006585767266514008465738854797447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-12071293476887015096166155669460000000000000)
      constant := (389318013843519970313847979599413819401084013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49476079170996267679/100000000000000000000)
  directionHi := (309225494818726673/625000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree002.table
  base := (79033646291932683539579289926522893588709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-13749774502986924366032539403040000000000000)
      constant := (240318652213891067479638336258205502216248047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree002.table
  base := (78707726420695889139524581900326575168087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-15186519778340042962083700084320000000000000)
      constant := (264026069799701436016150556627258182459348573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49476079170996267679/100000000000000000000)
  centralHi := (309225494818726673/625000000000000000)
  directionLo := (546638610755218117/781250000000000000)
  directionHi := (69969742176667918977/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree003.table
  base := (25949724131834887166314141370161920527699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-8281791268339895603495248666230000000000000)
      constant := (85364218152167818734585906719071816881356217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree003.table
  base := (25793792390981341696650143826767878873153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (40018)
      previous := (0)
      next := (29920)
      square := (1361091865354477128333132723315000000000000)
      linear := (-9150873039896535414000622249590000000000000)
      constant := (93696003517517767655653753344230086937753387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (546638610755218117/781250000000000000)
  centralHi := (69969742176667918977/100000000000000000000)
  directionLo := (85695082883465794441/100000000000000000000)
  directionHi := (42847541441732897221/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree004.table
  base := (34139802819689114662821718223251774157241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-19377390570372658047948455261880000000000000)
      constant := (129768623514467244084731124964994864895325803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree004.table
  base := (33874431089535746639051870829761963666571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-21416972381246098693918788914040000000000000)
      constant := (142445268118818835826357788469893282496029209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85695082883465794441/100000000000000000000)
  centralHi := (42847541441732897221/50000000000000000000)
  directionLo := (49476079170996267679/50000000000000000000)
  directionHi := (98952158341992535359/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree005.table
  base := (22382922573923000625715183139294769076061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-22191198604065524888906413191300000000000000)
      constant := (107718350810252696969803027479336819246283863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree005.table
  base := (22171131401222080474776295381180589767751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-24532198682699126559836333328900000000000000)
      constant := (118386364248819795641333750375523094871680429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49476079170996267679/50000000000000000000)
  centralHi := (98952158341992535359/100000000000000000000)
  directionLo := (110631876286509095933/100000000000000000000)
  directionHi := (55315938143254547967/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree006.table
  base := (14478771324683347537705502399042910449737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-25005006637758391729864371120720000000000000)
      constant := (98379063822225247981559567198400710826591771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree006.table
  base := (7158215433594837471903883138786803119097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (40018)
      previous := (0)
      next := (29920)
      square := (1361091865354477128333132723315000000000000)
      linear := (-13823712492076077212876938871880000000000000)
      constant := (54172333128711227551997415002143247115609363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110631876286509095933/100000000000000000000)
  centralHi := (55315938143254547967/50000000000000000000)
  directionLo := (15148893555310475399/12500000000000000000)
  directionHi := (121191148442483803193/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree007.table
  base := (9055119509694714914415443060184150134259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-27818814671451258570822329050140000000000000)
      constant := (97794624722344802203541181549500904837068697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree007.table
  base := (8934085269640318192035981453013321606729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7276)
      previous := (0)
      next := (5440)
      square := (247471248246268568787842313330000000000000)
      linear := (-2796604662327743844697402014420000000000000)
      constant := (9813190343295118066374943371690849944344681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15148893555310475399/12500000000000000000)
  centralHi := (121191148442483803193/100000000000000000000)
  directionLo := (65450700666499428779/50000000000000000000)
  directionHi := (130901401332998857559/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree008.table
  base := (2617909351735588015665281367531991215787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-15316311352572062705890143489780000000000000)
      constant := (51719548799967716444486366564514730675113921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree008.table
  base := (2573690819538378407792219592473046125693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (40018)
      previous := (0)
      next := (29920)
      square := (1361091865354477128333132723315000000000000)
      linear := (-16938938793529105078794483286740000000000000)
      constant := (57200288137629778974399496326231813633578047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65450700666499428779/50000000000000000000)
  centralHi := (130901401332998857559/100000000000000000000)
  directionLo := (139939484353335837953/100000000000000000000)
  directionHi := (69969742176667918977/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree009.table
  base := (2461227005413246969898825363998812089077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-33446430738836992252738244908980000000000000)
      constant := (113699034855568827900668701976918575252808991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree009.table
  base := (1198794054352195746664854134753067310717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (40018)
      previous := (0)
      next := (29920)
      square := (1361091865354477128333132723315000000000000)
      linear := (-18496551944255619011753255494170000000000000)
      constant := (62967452574961100759083644449395000980769343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139939484353335837953/100000000000000000000)
  centralHi := (69969742176667918977/50000000000000000000)
  directionLo := (74214118756494401519/50000000000000000000)
  directionHi := (148428237512988803039/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree010.table
  base := (18685906008187799089869053092068542971/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-9065059693132464773424050709600000000000000)
      constant := (31885849969932565272053577968572168046926965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree010.table
  base := (82117001088436167558113244238206485829/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7947500000000000000000000000000000000000000
      center := (20009)
      previous := (0)
      next := (14960)
      square := (680545932677238564166566361657500000000000)
      linear := (-10027082547491066472356013850800000000000000)
      constant := (35353901003262365072689804385683258418450391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74214118756494401519/50000000000000000000)
  centralHi := (148428237512988803039/100000000000000000000)
  directionLo := (78228549937581783193/50000000000000000000)
  directionHi := (156457099875163566387/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree011.table
  base := (-627670458168551597653378754634234113483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-19537023403111362967327080383910000000000000)
      constant := (72156521918517655498651780163044503050828511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree011.table
  base := (-1287209122396373581194809798165062587737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7276)
      previous := (0)
      next := (5440)
      square := (247471248246268568787842313330000000000000)
      linear := (-3929414226492481250485599983460000000000000)
      constant := (14556391569919124680644733617460296912144007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78228549937581783193/50000000000000000000)
  centralHi := (156457099875163566387/100000000000000000000)
  directionLo := (32818718141622532291/20000000000000000000)
  directionHi := (10255849419257041341/6250000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree012.table
  base := (-514436349709574185265072527416104943371/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-41887854839915592775612118697240000000000000)
      constant := (163586380896510005755895807826736847241307035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree012.table
  base := (-2594450651461537067842132014469290393807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-46338782792870321621259144232920000000000000)
      constant := (181588036457353325975062370470322125838087547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32818718141622532291/20000000000000000000)
  centralHi := (10255849419257041341/6250000000000000000)
  directionLo := (85695082883465794441/50000000000000000000)
  directionHi := (171390165766931588883/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree013.table
  base := (-367037502267629390496381497046837712309/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-22350831436804229808285038313330000000000000)
      constant := (92546823442568705823019220982764834377065765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree013.table
  base := (-1842917743445678615950232596431639548629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (40018)
      previous := (0)
      next := (29920)
      square := (1361091865354477128333132723315000000000000)
      linear := (-24727004547161674743588344323890000000000000)
      constant := (102762241620902304489972542346278817874908409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85695082883465794441/50000000000000000000)
  centralHi := (171390165766931588883/100000000000000000000)
  directionLo := (22298567544992863369/12500000000000000000)
  directionHi := (178388540359942906953/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree014.table
  base := (-288113875814062848994100905798679654963/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-11878867726825331614382008639020000000000000)
      constant := (52165536607275759105911233072619626218966684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree014.table
  base := (-2310248644749545320734679325426928224381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (40018)
      previous := (0)
      next := (29920)
      square := (1361091865354477128333132723315000000000000)
      linear := (-26284617697888188676547116531320000000000000)
      constant := (115870830857369438935875872589207795174692801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22298567544992863369/12500000000000000000)
  centralHi := (178388540359942906953/100000000000000000000)
  directionLo := (23140317137346315901/12500000000000000000)
  directionHi := (185122537098770527209/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree015.table
  base := (-1357221879052405912473060945074745437377/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-12582319735248548324621498121375000000000000)
      constant := (58545318454941013574459896133537008904042109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree015.table
  base := (-2718112319208674229739003112758461652827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (40018)
      previous := (0)
      next := (29920)
      square := (1361091865354477128333132723315000000000000)
      linear := (-27842230848614702609505888738750000000000000)
      constant := (130059720991546780881765222359915850405662967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23140317137346315901/12500000000000000000)
  centralHi := (185122537098770527209/100000000000000000000)
  directionLo := (191620030664908205183/100000000000000000000)
  directionHi := (1497031489569595353/781250000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree016.table
  base := (-6152154381294953424710865293679901089757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-53143086974687060139443950414920000000000000)
      constant := (261580156703266631525910009322480845158230569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree016.table
  base := (-615717723255028724564290321922223939771/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (40018)
      previous := (0)
      next := (29920)
      square := (1361091865354477128333132723315000000000000)
      linear := (-29399843999341216542464660946180000000000000)
      constant := (145290510182026173475971222375286250477339955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191620030664908205183/100000000000000000000)
  centralHi := (1497031489569595353/781250000000000000)
  directionLo := (197904316683985070717/100000000000000000000)
  directionHi := (98952158341992535359/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree017.table
  base := (-3397690935806128842274947699583852096907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-27978447504189963490200954172170000000000000)
      constant := (145406680561713368762052501135794754404617119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree017.table
  base := (-1359761733598219540228999049262578706159/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1870000000000000000000000000000000000000000
      center := (4708)
      previous := (0)
      next := (3520)
      square := (160128454747585544509780320390000000000000)
      linear := (-3642053782360909467696874488660000000000000)
      constant := (19004545286802057658701971715449488909741335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197904316683985070717/100000000000000000000)
  centralHi := (98952158341992535359/50000000000000000000)
  directionLo := (203995100363439470387/100000000000000000000)
  directionHi := (50998775090859867597/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree018.table
  base := (-736867753363720560649183906436872202279/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-29385351521036396910679933136880000000000000)
      constant := (160925873511877509027447850779932487204148215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree018.table
  base := (-7371008492886272762960534517413795945387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7276)
      previous := (0)
      next := (5440)
      square := (247471248246268568787842313330000000000000)
      linear := (-5911830963780771710614946429280000000000000)
      constant := (32506977422207614586805105652587412971783157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203995100363439470387/100000000000000000000)
  centralHi := (50998775090859867597/25000000000000000000)
  directionLo := (209909226530003756929/100000000000000000000)
  directionHi := (20990922653000375693/10000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree019.table
  base := (-3939263582007968806929516299654919855513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-30792255537882830331158912101590000000000000)
      constant := (177338307926260325138921905802749866056556021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree019.table
  base := (-3940054301923769366987822870155868402063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (40018)
      previous := (0)
      next := (29920)
      square := (1361091865354477128333132723315000000000000)
      linear := (-34072683451520758341340977568470000000000000)
      constant := (197029668285335004902917691675989494349841723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209909226530003756929/100000000000000000000)
  centralHi := (20990922653000375693/10000000000000000000)
  directionLo := (215661229228990354921/100000000000000000000)
  directionHi := (107830614614495177461/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree020.table
  base := (-8329094565416574652315481661594026161531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-64398319109458527503275782132600000000000000)
      constant := (389275963366631441506600004097624422576306127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree020.table
  base := (-4165082524726684253113817384095569806939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (40018)
      previous := (0)
      next := (29920)
      square := (1361091865354477128333132723315000000000000)
      linear := (-35630296602247272274299749775900000000000000)
      constant := (216256065238181381463542293687960183583740919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215661229228990354921/100000000000000000000)
  centralHi := (107830614614495177461/50000000000000000000)
  directionLo := (110631876286509095933/50000000000000000000)
  directionHi := (221263752573018191867/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree021.table
  base := (-8723054145257099673321158825793681939409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-67212127143151394344233740062020000000000000)
      constant := (425642079249501346892105178103746814968683853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree021.table
  base := (-8723777305889012835809151163113285160929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-74375819505947572414517043966660000000000000)
      constant := (472926869626569107664985241292492866473406709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110631876286509095933/50000000000000000000)
  centralHi := (221263752573018191867/100000000000000000000)
  directionLo := (226727877890718381873/100000000000000000000)
  directionHi := (113363938945359190937/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree022.table
  base := (-4531062256008560389141576047607573293479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-35012967588422130592595848995720000000000000)
      constant := (231885004376441828139001349455167366194900043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree022.table
  base := (-453130608610602667153742317755590866559/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (1819)
      previous := (0)
      next := (1360)
      square := (61867812061567142196960578332500000000000)
      linear := (-1761160131986377279100786099580000000000000)
      constant := (11711323983342840728373407004673171197822245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226727877890718381873/100000000000000000000)
  centralHi := (113363938945359190937/50000000000000000000)
  directionLo := (232063381477912615487/100000000000000000000)
  directionHi := (3625990335592384617/1562500000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree023.table
  base := (-9347410608093391758411509221810038228423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-72839743210537128026149655920860000000000000)
      constant := (503656566327848528484233998848511659787456491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree023.table
  base := (-9347738941427422799099333155303173287143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-80606272108853628146352132796380000000000000)
      constant := (559622888115447734798172393988761212120172403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232063381477912615487/100000000000000000000)
  centralHi := (3625990335592384617/1562500000000000000)
  directionLo := (237278940138179744651/100000000000000000000)
  directionHi := (59319735034544936163/25000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree024.table
  base := (-2394905795968067127391384847245007366117/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-18913387811057498716776903462570000000000000)
      constant := (136324925720258024865759172385632643763484689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree024.table
  base := (-1197480491914843233279347620149268278559/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7947500000000000000000000000000000000000000
      center := (20009)
      previous := (0)
      next := (14960)
      square := (680545932677238564166566361657500000000000)
      linear := (-20930374602576664003067419302810000000000000)
      constant := (151474646588676798278148788031810952284921878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237278940138179744651/100000000000000000000)
  centralHi := (59319735034544936163/25000000000000000000)
  directionLo := (48476459376993521277/20000000000000000000)
  directionHi := (121191148442483803193/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree025.table
  base := (-9759219655089221182410931737698811279799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-78467359277922861708065571779700000000000000)
      constant := (588698099682869008770041589198964327080339483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree025.table
  base := (-1951873577915089464019025447316686467521/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-86836724711759683878187221626100000000000000)
      constant := (654123948886106685630021475423651268598753705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48476459376993521277/20000000000000000000)
  centralHi := (121191148442483803193/50000000000000000000)
  directionLo := (247380395854981338397/100000000000000000000)
  directionHi := (123690197927490669199/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree026.table
  base := (-4943247273955490978717096818892823697821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-40640583655807864274511764854560000000000000)
      constant := (316925453807210283764453048535311989279182057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree026.table
  base := (-9886593976244390949178745439521155138601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-89951951013212711744104766040960000000000000)
      constant := (704298075505709232366815034654842247814387421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247380395854981338397/100000000000000000000)
  centralHi := (123690197927490669199/50000000000000000000)
  directionLo := (252279493148971501729/100000000000000000000)
  directionHi := (25227949314897150173/10000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree027.table
  base := (-622602350137120890882407152823151270429/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-21023743836327148847495371909635000000000000)
      constant := (170189394913920205585315044561090919549412772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree027.table
  base := (-996170422723301393128292246410846897723/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (40018)
      previous := (0)
      next := (29920)
      square := (1361091865354477128333132723315000000000000)
      linear := (-46533588657332869805011155227910000000000000)
      constant := (378210193767040545267379127392234588560692915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252279493148971501729/100000000000000000000)
  centralHi := (25227949314897150173/10000000000000000000)
  directionLo := (64271312162599345831/25000000000000000000)
  directionHi := (10283409946015895333/4000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree028.table
  base := (-9984771116011242650141897413149367051357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-86908783379001462230939445567960000000000000)
      constant := (729417763221304839729658149340930374790937769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree028.table
  base := (-2496203930071360299781717469323437945813/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7947500000000000000000000000000000000000000
      center := (20009)
      previous := (0)
      next := (14960)
      square := (680545932677238564166566361657500000000000)
      linear := (-24045600904029691868984963717670000000000000)
      constant := (202622628195268421743184190560300790770260473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64271312162599345831/25000000000000000000)
  centralHi := (10283409946015895333/4000000000000000000)
  directionLo := (65450700666499428779/25000000000000000000)
  directionHi := (261802802665997715117/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree029.table
  base := (-9955973959681764399496923232946811953859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-89722591412694329071897403497380000000000000)
      constant := (779831230928163354230839400227524341137024503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree029.table
  base := (-2489000949379437411562888469880278893277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (1819)
      previous := (0)
      next := (1360)
      square := (61867812061567142196960578332500000000000)
      linear := (-2256764316308449894133122711035000000000000)
      constant := (19693368448502273028095086942587099399842947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65450700666499428779/25000000000000000000)
  centralHi := (261802802665997715117/100000000000000000000)
  directionLo := (133218420173324783967/50000000000000000000)
  directionHi := (53287368069329913587/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree030.table
  base := (-2468824256323850972178833752349611683513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-23134099861596798978213840356700000000000000)
      constant := (207999459013590292874608228883226069516432021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree030.table
  base := (-9875316970832597349772592014307561248731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-102412856219024823207774943700400000000000000)
      constant := (924473330173821519297948896311516262790284151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133218420173324783967/50000000000000000000)
  centralHi := (53287368069329913587/20000000000000000000)
  directionLo := (270991646188661545947/100000000000000000000)
  directionHi := (67747911547165386487/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree031.table
  base := (-9742773171090353266665487873977117993413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 930000000000000000000000000000000000000000
      center := (2332)
      previous := (0)
      next := (1760)
      square := (79636076425269816253527111210000000000000)
      linear := (-3075813144518711701735913527620000000000000)
      constant := (28577983350632180115072620239130128026612591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree031.table
  base := (-1217848311920622859247566317645544174711/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7947500000000000000000000000000000000000000
      center := (20009)
      previous := (0)
      next := (14960)
      square := (680545932677238564166566361657500000000000)
      linear := (-26382020630119462768423122028815000000000000)
      constant := (246096442185041011180538082048817130137187462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270991646188661545947/100000000000000000000)
  centralHi := (67747911547165386487/25000000000000000000)
  directionLo := (275471150420829753553/100000000000000000000)
  directionHi := (137735575210414876777/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree032.table
  base := (-4779211812735340179923453246113999233571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-49082007756886464797385638642820000000000000)
      constant := (470795056586191831446748103128573340209614807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree032.table
  base := (-4779216260679210021719081703693028678879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (40018)
      previous := (0)
      next := (29920)
      square := (1361091865354477128333132723315000000000000)
      linear := (-54321654410965439469805016265060000000000000)
      constant := (523122731687751729530254499583319861829843659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275471150420829753553/100000000000000000000)
  centralHi := (137735575210414876777/50000000000000000000)
  directionLo := (139939484353335837953/50000000000000000000)
  directionHi := (279878968706671675907/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree033.table
  base := (-932226211310807203629546989358618963713/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-50488911773732898217864617607530000000000000)
      constant := (499507842197245468118310206411690507638077105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree033.table
  base := (-9322268049305842586800218449480276183291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7276)
      previous := (0)
      next := (5440)
      square := (247471248246268568787842313330000000000000)
      linear := (-10159866829398536982320688813180000000000000)
      constant := (100913852068297520544511411766670200183028901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139939484353335837953/50000000000000000000)
  centralHi := (279878968706671675907/100000000000000000000)
  directionLo := (35527304537857919311/12500000000000000000)
  directionHi := (284218436302863354489/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree034.table
  base := (-1806859502937095111325147284633438492849/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-103791631581158663276687193144480000000000000)
      constant := (1058194171932910466644272075402768984125581665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree034.table
  base := (-9034301474032836546084730766632216319851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1870000000000000000000000000000000000000000
      center := (4708)
      previous := (0)
      next := (3520)
      square := (160128454747585544509780320390000000000000)
      linear := (-6757280083813937333614418903520000000000000)
      constant := (69165086481195371028348622671479775548187863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35527304537857919311/12500000000000000000)
  centralHi := (284218436302863354489/100000000000000000000)
  directionLo := (36061579698954598739/12500000000000000000)
  directionHi := (288492637591636789913/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree035.table
  base := (-1738907116448813631328952234666675874821/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-106605439614851530117645151073900000000000000)
      constant := (1119125559204507540145619454164029867264455285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree035.table
  base := (-8694538221949739501234069326127069841529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-117988987726289962537362665774700000000000000)
      constant := (1243507738412090740370775376164992044973779309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36061579698954598739/12500000000000000000)
  centralHi := (288492637591636789913/100000000000000000000)
  directionLo := (58540886346113406079/20000000000000000000)
  directionHi := (73176107932641757599/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree036.table
  base := (-4151490023001043056750210535613820295699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-54709623824272198479301554501660000000000000)
      constant := (590904917727531490776822609963105356087499783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree036.table
  base := (-8302981805231417542577956447200378663063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-121104214027742990403280210189560000000000000)
      constant := (1313156166281377125355013714430029996230122723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58540886346113406079/20000000000000000000)
  centralHi := (73176107932641757599/25000000000000000000)
  directionLo := (74214118756494401519/25000000000000000000)
  directionHi := (296856475025977606077/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree037.table
  base := (-982454166109207135699507699161735218557/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-28058263920559315949890266733185000000000000)
      constant := (311561748424828840207293131920180934729800338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree037.table
  base := (-3929817250454881378661607453982657240017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (40018)
      previous := (0)
      next := (29920)
      square := (1361091865354477128333132723315000000000000)
      linear := (-62109720164598009134598877302210000000000000)
      constant := (692375873274748038744705555299324132633985957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74214118756494401519/25000000000000000000)
  centralHi := (296856475025977606077/100000000000000000000)
  directionLo := (300951240527404300753/100000000000000000000)
  directionHi := (150475620263702150377/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree038.table
  base := (-368224850398032972872184971261004161697/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-28761715928982532660129756215540000000000000)
      constant := (328109257347619990647413308330682625009137745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree038.table
  base := (-7364497788556022670662606454464383383213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-127334666630649046135115299019280000000000000)
      constant := (1458294474512890600891379775080177725224765873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300951240527404300753/100000000000000000000)
  centralHi := (150475620263702150377/50000000000000000000)
  directionLo := (15249551762684555017/5000000000000000000)
  directionHi := (304991035253691100341/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree039.table
  base := (-6817572112767377441241989748261640075471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-117860671749622997481476982791580000000000000)
      constant := (1380379939560495935451318613964671691662417107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree039.table
  base := (-136351452650257859266092540545805330733/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (40018)
      previous := (0)
      next := (29920)
      square := (1361091865354477128333132723315000000000000)
      linear := (-65224946466051037000516421717070000000000000)
      constant := (766892173552957632995973699639737121339994825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15249551762684555017/5000000000000000000)
  centralHi := (304991035253691100341/100000000000000000000)
  directionLo := (308978015391472372497/100000000000000000000)
  directionHi := (154489007695736186249/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree040.table
  base := (-248754372720089996264272000206574222951/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-120674479783315864322434940721000000000000000)
      constant := (1450075722264178850153066123769111162880806675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree040.table
  base := (-6218859663979353687591341080974097514687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7276)
      previous := (0)
      next := (5440)
      square := (247471248246268568787842313330000000000000)
      linear := (-12142283566686827442450035259000000000000000)
      constant := (146474669301998955927701687299598485818255457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308978015391472372497/100000000000000000000)
  centralHi := (154489007695736186249/50000000000000000000)
  directionLo := (312914199750327132773/100000000000000000000)
  directionHi := (156457099875163566387/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree041.table
  base := (-5568359068291585029666021024367644477907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-123488287817008731163392898650420000000000000)
      constant := (1521524376219671060223119053477658080970194119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree041.table
  base := (-5568359298545272944166879023386778327751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-136680345535008129732867932263860000000000000)
      constant := (1690605518839950157837745567561883431696079571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312914199750327132773/100000000000000000000)
  centralHi := (156457099875163566387/50000000000000000000)
  directionLo := (9900046303529772653/3125000000000000000)
  directionHi := (316801481712952724897/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree042.table
  base := (-304129478680808845897965778078737988071/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-31575523962675399501087714144960000000000000)
      constant := (398681475143936255965083974179605993521565228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree042.table
  base := (-973214362419957197789697395708755561923/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-139795571836461157598785476678720000000000000)
      constant := (1771936815782748632912467495650129330343233915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9900046303529772653/3125000000000000000)
  centralHi := (316801481712952724897/100000000000000000000)
  directionLo := (160320819940562469117/50000000000000000000)
  directionHi := (64128327976224987647/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree043.table
  base := (-4111997287960693100131071092363599591099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-129115903884394464845308814509260000000000000)
      constant := (1669680294761121681746948860340905742378861583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree043.table
  base := (-822399477976672801287826573046000573403/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-142910798137914185464703021093580000000000000)
      constant := (1855215252561504482533349409546503820885759315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160320819940562469117/50000000000000000000)
  centralHi := (64128327976224987647/20000000000000000000)
  directionLo := (162218173793653358663/50000000000000000000)
  directionHi := (324436347587306717327/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree044.table
  base := (-3306136090410236685110656517818634122269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-131929711918087331686266772438680000000000000)
      constant := (1746387558386839944452600597861688877825498473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree044.table
  base := (-413267019775549957753907360912737115863/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (1819)
      previous := (0)
      next := (1360)
      square := (61867812061567142196960578332500000000000)
      linear := (-3318773282712891212059558307010000000000000)
      constant := (44100927926697348327661562170112437947031186) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (162218173793653358663/50000000000000000000)
  centralHi := (324436347587306717327/100000000000000000000)
  directionLo := (32818718141622532291/10000000000000000000)
  directionHi := (328187181416225322911/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree045.table
  base := (-1224244079936816902699147657487048548339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-67371759975890099263612365184050000000000000)
      constant := (912423845591479289313198811821839839035138663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree045.table
  base := (-1224244102480231896022404947577446565591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (40018)
      previous := (0)
      next := (29920)
      square := (1361091865354477128333132723315000000000000)
      linear := (-74570625370410120598269054961650000000000000)
      constant := (1013806772071429393437542184393026297367986211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32818718141622532291/10000000000000000000)
  centralHi := (328187181416225322911/100000000000000000000)
  directionLo := (331895628859527287799/100000000000000000000)
  directionHi := (1659478144297636439/500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree046.table
  base := (-307810712588959152687486806401577424307/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-137557327985473065368182688297520000000000000)
      constant := (1905060692957487337983395481288481261428614595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree046.table
  base := (-1539053592926013525709230491300938118489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-152256477042273269062455654338160000000000000)
      constant := (2116733398466470864693455905058434317721323469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331895628859527287799/100000000000000000000)
  centralHi := (1659478144297636439/500000000000000000)
  directionLo := (335563095208927546629/100000000000000000000)
  directionHi := (33556309520892754663/10000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree047.table
  base := (-288916174214949687120551159767856134783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-70185568009582966104570323113470000000000000)
      constant := (993513281784859007382955803156684270763420611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree047.table
  base := (-72229046045499826972000342015120049767/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7947500000000000000000000000000000000000000
      center := (20009)
      previous := (0)
      next := (14960)
      square := (680545932677238564166566361657500000000000)
      linear := (-38842925835931574232093299688255000000000000)
      constant := (551950097899612410652056595708035366723581414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335563095208927546629/100000000000000000000)
  centralHi := (33556309520892754663/10000000000000000000)
  directionLo := (42398863722305854997/12500000000000000000)
  directionHi := (339190909778446839977/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree048.table
  base := (43517544663941842788858277282321599229/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-71592472026429399525049302078180000000000000)
      constant := (1035372651456444199846176497632144665852886035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree048.table
  base := (435175433386950866188444146736825653759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-158486929645179324794290743167880000000000000)
      constant := (2300814523426453615621886123605196368753299861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42398863722305854997/12500000000000000000)
  centralHi := (339190909778446839977/100000000000000000000)
  directionLo := (68556066306772635553/20000000000000000000)
  directionHi := (171390165766931588883/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree049.table
  base := (374992448273025880381038836631297123357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-36499688021637916472764140521445000000000000)
      constant := (539054227725724585932661065988935529606638231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree049.table
  base := (23437027879414770810307816114354104981/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7947500000000000000000000000000000000000000
      center := (20009)
      previous := (0)
      next := (14960)
      square := (680545932677238564166566361657500000000000)
      linear := (-40400538986658088165052071895685000000000000)
      constant := (598943948465332496783287957055748007195753584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68556066306772635553/20000000000000000000)
  centralHi := (171390165766931588883/50000000000000000000)
  directionLo := (86583138549243468439/25000000000000000000)
  directionHi := (346332554196973873757/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree050.table
  base := (1308275333532899411034423915877403978393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-74406280060122266366007260007600000000000000)
      constant := (1121720693735476335702946465741974555669707019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree050.table
  base := (1308275330605090574294398897147135839531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (40018)
      previous := (0)
      next := (29920)
      square := (1361091865354477128333132723315000000000000)
      linear := (-82358691124042690263062915998800000000000000)
      constant := (1246342101414801895096916214146530744833869049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86583138549243468439/25000000000000000000)
  centralHi := (346332554196973873757/100000000000000000000)
  directionLo := (174924355441669797441/50000000000000000000)
  directionHi := (349848710883339594883/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree051.table
  base := (151396721933571390036230175112193731859/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-151626368153937399572972477944620000000000000)
      constant := (2332418732558753606672946458281321363223737425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree051.table
  base := (94622951111185886863399885675813457601/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42500000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (80)
      square := (3639283062445126011585916372500000000000)
      linear := (-224375145119703754534817348145000000000000)
      constant := (3464625334583659682606576719087388287792170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174924355441669797441/50000000000000000000)
  centralHi := (349848710883339594883/100000000000000000000)
  directionLo := (353329878324589508567/100000000000000000000)
  directionHi := (44166234790573688571/12500000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree052.table
  base := (2502535959619741245108409959914272099769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-77220088093815133206965217937020000000000000)
      constant := (1211574473057674831650017695797952846463634027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree052.table
  base := (5005071916653014380923179996351626329471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-170947834850991436257960920827320000000000000)
      constant := (2692342436123122970921227079325521820101388309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353329878324589508567/100000000000000000000)
  centralHi := (44166234790573688571/12500000000000000000)
  directionLo := (71355416143977162781/20000000000000000000)
  directionHi := (178388540359942906953/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree053.table
  base := (6277012263922077696391078023883150513519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-157253984221323133254888393803460000000000000)
      constant := (2515632028095061683034529315198645122930475277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree053.table
  base := (1255402452440652813197004545349183143639/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-174063061152444464123878465242180000000000000)
      constant := (2795092260343572779752543528460195266068141905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71355416143977162781/20000000000000000000)
  centralHi := (178388540359942906953/50000000000000000000)
  directionLo := (72038258651119158901/20000000000000000000)
  directionHi := (180095646627797897253/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree054.table
  base := (3800369533947674918775099089125213657179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-80033896127508000047923175866440000000000000)
      constant := (1304933989228055017791511501112127990973647057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree054.table
  base := (7600739066753199191568861507511245972303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-177178287453897491989796009657040000000000000)
      constant := (2899789222884324160693681420431458250945951237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72038258651119158901/20000000000000000000)
  centralHi := (180095646627797897253/50000000000000000000)
  directionLo := (363573445327451409577/100000000000000000000)
  directionHi := (181786722663725704789/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree055.table
  base := (897625231770252176950076778441395622603/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-81440800144354433468402154831150000000000000)
      constant := (1352928398579849416219403422075607717899822245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree055.table
  base := (8976252316943606972839041148351927953059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7276)
      previous := (0)
      next := (5440)
      square := (247471248246268568787842313330000000000000)
      linear := (-16390319432304592714155777642900000000000000)
      constant := (273312120336628016027422564308123707178434051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363573445327451409577/100000000000000000000)
  centralHi := (181786722663725704789/50000000000000000000)
  directionLo := (366924423495367762271/100000000000000000000)
  directionHi := (11466388234230242571/3125000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree056.table
  base := (1300444000088450981450034305241019373767/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-41423852080600433444440566897930000000000000)
      constant := (700899621042349631749977119432259717709140522) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree056.table
  base := (10403552000203365294092237087214032074533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-183408740056803547721631098486760000000000000)
      constant := (3115024562759361229370623020551133407964940407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366924423495367762271/100000000000000000000)
  centralHi := (11466388234230242571/3125000000000000000)
  directionLo := (23140317137346315901/6250000000000000000)
  directionHi := (370245074197541054417/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree057.table
  base := (11882638104948989593882042051733156048711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-168509216356094600618720225521140000000000000)
      constant := (2903093039450723773159753975764136688888433813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree057.table
  base := (2376527620922794898041133487200162244541/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-186523966358256575587548642901620000000000000)
      constant := (3225562940015794409465180536294516578876979195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23140317137346315901/6250000000000000000)
  centralHi := (370245074197541054417/100000000000000000000)
  directionLo := (373536206247369508439/100000000000000000000)
  directionHi := (9338405156184237711/2500000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree058.table
  base := (3353377654759361606904791498777967311579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-42830756097446866864919545862640000000000000)
      constant := (751085115742709862004675918060186879759282257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree058.table
  base := (13413510618814875192715299721639499513457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-189639192659709603453466187316480000000000000)
      constant := (3338048455436092498352973595387611968953279803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373536206247369508439/100000000000000000000)
  centralHi := (9338405156184237711/2500000000000000000)
  directionLo := (188399296567033433093/50000000000000000000)
  directionHi := (376798593134066866187/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree059.table
  base := (14996169532083487671939671868495934058477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-174136832423480334300636141379980000000000000)
      constant := (3107340754698351149943803664953383777890589191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree059.table
  base := (3749042382983906587428280557161145899247/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7947500000000000000000000000000000000000000
      center := (20009)
      previous := (0)
      next := (14960)
      square := (680545932677238564166566361657500000000000)
      linear := (-48188604740290657829845932932835000000000000)
      constant := (863120277246424590982496657146722782813706213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188399296567033433093/50000000000000000000)
  centralHi := (376798593134066866187/100000000000000000000)
  directionLo := (5938015236648571783/1562500000000000000)
  directionHi := (380032975145508594113/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree060.table
  base := (16630614833644107640160657725289782721161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-176950640457173201141594099309400000000000000)
      constant := (3212093914603151693540347147590010443585107163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree060.table
  base := (16630614833545882648647548865539309078317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-195869645262615659185301276146200000000000000)
      constant := (3568860900631453938447618143707549463559969743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5938015236648571783/1562500000000000000)
  centralHi := (380032975145508594113/100000000000000000000)
  directionLo := (191620030664908205183/50000000000000000000)
  directionHi := (383240061329816410367/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree061.table
  base := (18316846513682516133712487711584587049261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-179764448490866067982552057238820000000000000)
      constant := (3318599942656305012665857859983808364463019463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree061.table
  base := (1831684651361726740121844303001798847133/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (40018)
      previous := (0)
      next := (29920)
      square := (1361091865354477128333132723315000000000000)
      linear := (-99492435782034343525609410280530000000000000)
      constant := (1843593915170739506206881003245428592675179035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191620030664908205183/50000000000000000000)
  centralHi := (383240061329816410367/100000000000000000000)
  directionLo := (193210265655202786827/50000000000000000000)
  directionHi := (77284106262081114731/20000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree062.table
  base := (250685807031707851772229797375685855147/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 232500000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (440)
      square := (19909019106317454063381777802500000000000)
      linear := (-1472405294552894635673467864260000000000000)
      constant := (27635958377660929969630250250428775690573420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree062.table
  base := (20054864562493286487836110533139963574751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7276)
      previous := (0)
      next := (5440)
      square := (247471248246268568787842313330000000000000)
      linear := (-18372736169592883174285124088720000000000000)
      constant := (346132899825915962820203870828197449473103039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193210265655202786827/50000000000000000000)
  centralHi := (77284106262081114731/20000000000000000000)
  directionLo := (194787518483828183539/50000000000000000000)
  directionHi := (389575036967656367079/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree063.table
  base := (10922334485446774604313656172057654708273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-92696032279125900832233986548830000000000000)
      constant := (1768435301548626764764677045440737218523951059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree063.table
  base := (682645905339523764497735975421695753247/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7947500000000000000000000000000000000000000
      center := (20009)
      previous := (0)
      next := (14960)
      square := (680545932677238564166566361657500000000000)
      linear := (-51303831041743685695763477347695000000000000)
      constant := (982420775958162448204690573513092066396577704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194787518483828183539/50000000000000000000)
  centralHi := (389575036967656367079/100000000000000000000)
  directionLo := (15708168159959862907/4000000000000000000)
  directionHi := (98176050999749143169/25000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree064.table
  base := (4737251945953647844471161843785841321491/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-188205872591944668505425931027080000000000000)
      constant := (3648635235432295781908849352310332902649292765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree064.table
  base := (23686259729749117622071365925765500419853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-208330550468427770648971453805640000000000000)
      constant := (4053851447555646022345428523434488525834712687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15708168159959862907/4000000000000000000)
  centralHi := (98176050999749143169/25000000000000000000)
  directionLo := (79161726673594028287/20000000000000000000)
  directionHi := (98952158341992535359/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree065.table
  base := (25579636830485154367121001124275798953873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-191019680625637535346383888956500000000000000)
      constant := (3762152735810070480551561811644037128384015859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree065.table
  base := (25579636830472454174406307617825845277431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-211445776769880798514888998220500000000000000)
      constant := (4179966929226489939460630362877818362136953149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79161726673594028287/20000000000000000000)
  centralHi := (98952158341992535359/25000000000000000000)
  directionLo := (79777780530359428443/20000000000000000000)
  directionHi := (49861112831474642777/12500000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree066.table
  base := (27524800264662069711891506368712767006047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-193833488659330402187341846885920000000000000)
      constant := (3877423104206411670981327995466158907278433501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree066.table
  base := (5504960052930726957576840993504553971139/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7276)
      previous := (0)
      next := (5440)
      square := (247471248246268568787842313330000000000000)
      linear := (-19505545733757620580073322057760000000000000)
      constant := (391639049892594355903691606886294080488295855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79777780530359428443/20000000000000000000)
  centralHi := (49861112831474642777/12500000000000000000)
  directionLo := (50243195911997873339/12500000000000000000)
  directionHi := (401945567295982986713/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree067.table
  base := (29521750024195548167853355644688090041407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-196647296693023269028299804815340000000000000)
      constant := (3994446340597957144071097230263025763589376381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree067.table
  base := (29521750024189946247046462444405476773887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-217676229372786854246724087050220000000000000)
      constant := (4438039306306031423473417586857435010664186773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50243195911997873339/12500000000000000000)
  centralHi := (401945567295982986713/100000000000000000000)
  directionLo := (404979161783695086267/100000000000000000000)
  directionHi := (101244790445923771567/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree068.table
  base := (3946310762655961745861108425963579336591/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-49865276181679033967314440686190000000000000)
      constant := (1028305611240527561580346560035465998454783706) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree068.table
  base := (7892621525310993417168775775199238195291/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 467500000000000000000000000000000000000000
      center := (1177)
      previous := (0)
      next := (880)
      square := (40032113686896386127445080097500000000000)
      linear := (-3246933171679998266362376933310000000000000)
      constant := (67205826495059637105078090404202257542519417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (404979161783695086267/100000000000000000000)
  centralHi := (101244790445923771567/25000000000000000000)
  directionLo := (203995100363439470387/50000000000000000000)
  directionHi := (16319608029075157631/4000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree069.table
  base := (2104438030514621377070169218059514032333/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-50568728190102250677553930168545000000000000)
      constant := (1058437854319251169154611609173489815820864156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree069.table
  base := (33671008488231471426790540451241549196873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-223906681975692909978559175879940000000000000)
      constant := (4703900234868499297111296252196926884896859267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203995100363439470387/50000000000000000000)
  centralHi := (16319608029075157631/4000000000000000000)
  directionLo := (41097917988542151951/10000000000000000000)
  directionHi := (410979179885421519511/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree070.table
  base := (895582929445292730713021863161608425053/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-51272180198525467387793419650900000000000000)
      constant := (1089008314380367941943831448498199170894277990) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree070.table
  base := (1432932687112402743387288296182061488009/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-227021908277145937844476720294800000000000000)
      constant := (4839751405896021948163573008208069336759515275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41097917988542151951/10000000000000000000)
  centralHi := (410979179885421519511/100000000000000000000)
  directionLo := (25871661070004849911/6250000000000000000)
  directionHi := (413946577120077598577/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree071.table
  base := (3802741216286978285734822464476234062049/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-103951264413897368196065818266510000000000000)
      constant := (2240033982837504946795109946122679914004436335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree071.table
  base := (19013706081434346700352743093439225831001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (40018)
      previous := (0)
      next := (29920)
      square := (1361091865354477128333132723315000000000000)
      linear := (-115068567289299482855197132354830000000000000)
      constant := (2488774857362008589617726087808058298916752179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25871661070004849911/6250000000000000000)
  centralHi := (413946577120077598577/100000000000000000000)
  directionLo := (416892853284345762663/100000000000000000000)
  directionHi := (52111606660543220333/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree072.table
  base := (40283293436518354744370299458393084827247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-210716336861487603233089594462440000000000000)
      constant := (4605855541717755737093927787926387263556953101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree072.table
  base := (629426459945587989447684168226270783179/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7947500000000000000000000000000000000000000
      center := (20009)
      previous := (0)
      next := (14960)
      square := (680545932677238564166566361657500000000000)
      linear := (-58313090220012998394077952281130000000000000)
      constant := (1279323790332645646942955161677541037115616656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (416892853284345762663/100000000000000000000)
  centralHi := (52111606660543220333/12500000000000000000)
  directionLo := (419818453060007513859/100000000000000000000)
  directionHi := (20990922653000375693/5000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree073.table
  base := (2661935062004976959233532880661652032543/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-53382536223795117518511888097965000000000000)
      constant := (1183348996407614304876323569858037671239285876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree073.table
  base := (4259096099207915100046644909214579036089/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3638)
      previous := (0)
      next := (2720)
      square := (123735624123134284393921156665000000000000)
      linear := (-10743981235522955520101334251790000000000000)
      constant := (239044897531567712081444575326700066707148605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (419818453060007513859/100000000000000000000)
  centralHi := (20990922653000375693/5000000000000000000)
  directionLo := (84544761148123760727/20000000000000000000)
  directionHi := (105680951435154700909/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree074.table
  base := (22475207411539482719533099925464421784157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-108171976464436668457502755160640000000000000)
      constant := (2431344648697223966432448897570093928003724631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree074.table
  base := (44950414823078646502202083403854178752589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-239482813482958049308146897954240000000000000)
      constant := (5402627467795155641056745455000732434254480431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84544761148123760727/20000000000000000000)
  centralHi := (105680951435154700909/25000000000000000000)
  directionLo := (212804662983431306277/50000000000000000000)
  directionHi := (85121865193372522511/20000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree075.table
  base := (47361654923236465300421002513532553877099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-219157760962566203755963468250700000000000000)
      constant := (4993735476991622949349922163605264352827676417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree075.table
  base := (47361654923236253543158415735726227261853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-242598039784411077174064442369100000000000000)
      constant := (5548214327612616824999294869212623676465430687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212804662983431306277/50000000000000000000)
  centralHi := (85121865193372522511/20000000000000000000)
  directionLo := (428475414417328972207/100000000000000000000)
  directionHi := (26779713401083060763/6250000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree076.table
  base := (996493625729180894611716444615707953649/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-110985784498129535298460713090060000000000000)
      constant := (2563267262202207950721132108685357150759251675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree076.table
  base := (24912340643229452070057492319529272152931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (40018)
      previous := (0)
      next := (29920)
      square := (1361091865354477128333132723315000000000000)
      linear := (-122856633042932052519990993391980000000000000)
      constant := (2847874162563751677250385526438823556174167649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428475414417328972207/100000000000000000000)
  centralHi := (26779713401083060763/6250000000000000000)
  directionLo := (215661229228990354921/50000000000000000000)
  directionHi := (431322458457980709843/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree077.table
  base := (52339493906832882453946453568858562804351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-224785377029951937437879384109540000000000000)
      constant := (5261086439615777242404328202170809236564943933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree077.table
  base := (52339493906832789116224851980179439022169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7276)
      previous := (0)
      next := (5440)
      square := (247471248246268568787842313330000000000000)
      linear := (-22620772035210648445990866472620000000000000)
      constant := (531384496392819566380725235424441857877406841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215661229228990354921/50000000000000000000)
  centralHi := (431322458457980709843/100000000000000000000)
  directionLo := (217075416376642697151/50000000000000000000)
  directionHi := (434150832753285394303/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree078.table
  base := (13726523194654065864978631686954894459469/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-56899796265911201069709335509740000000000000)
      constant := (1349347805652288401965146961982500960726649127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree078.table
  base := (54906092778616201495550563829368789561881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-251943718688770160771817075613680000000000000)
      constant := (5996657733174899565584409313543683382017219699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217075416376642697151/50000000000000000000)
  centralHi := (434150832753285394303/100000000000000000000)
  directionLo := (218480449920871568033/50000000000000000000)
  directionHi := (436960899841743136067/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree079.table
  base := (7190559737029097226525330423606923963451/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-57603248274334417779948824992095000000000000)
      constant := (1383862218342117051991181646280545023573258466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree079.table
  base := (7190559737029092084667721237914804987147/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7947500000000000000000000000000000000000000
      center := (20009)
      previous := (0)
      next := (14960)
      square := (680545932677238564166566361657500000000000)
      linear := (-63764736247555797159433655007135000000000000)
      constant := (1537508285917857242616070215237869830108280626) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218480449920871568033/50000000000000000000)
  centralHi := (436960899841743136067/100000000000000000000)
  directionLo := (439753010678313113649/100000000000000000000)
  directionHi := (8795060213566262273/2000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree080.table
  base := (7524331156783106855789182877600154787439/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-58306700282757634490188314474450000000000000)
      constant := (1418814847969525546622749645292242492504373274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree080.table
  base := (7524331156783103442515917482018681362289/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7947500000000000000000000000000000000000000
      center := (20009)
      previous := (0)
      next := (14960)
      square := (680545932677238564166566361657500000000000)
      linear := (-64543542822919054125913041110850000000000000)
      constant := (1576338922948345249737108877130674776101433462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (439753010678313113649/100000000000000000000)
  centralHi := (8795060213566262273/2000000000000000000)
  directionLo := (110631876286509095933/25000000000000000000)
  directionHi := (442527505146036383733/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree081.table
  base := (15729151711861903153054500760258647077261/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-59010152291180851200427803956805000000000000)
      constant := (1454205694530719222194367569806753179523743463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree081.table
  base := (62916606847447594486518503262483949574011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-261289397593129244369569708858260000000000000)
      constant := (6462625377524018598796774355075066475695780969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110631876286509095933/25000000000000000000)
  centralHi := (442527505146036383733/100000000000000000000)
  directionLo := (89056942507793281823/20000000000000000000)
  directionHi := (111321178134741602279/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree082.table
  base := (16422587667665751011101873390904513292293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-59713604299604067910667293439160000000000000)
      constant := (1490034758022009246283569973928787711821680719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree082.table
  base := (8211293833832874001643958299142925166951/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7947500000000000000000000000000000000000000
      center := (20009)
      previous := (0)
      next := (14960)
      square := (680545932677238564166566361657500000000000)
      linear := (-66101155973645568058871813318280000000000000)
      constant := (1655460550211767875838526134035880718211474458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89056942507793281823/20000000000000000000)
  centralHi := (111321178134741602279/25000000000000000000)
  directionLo := (224012476009174899447/50000000000000000000)
  directionHi := (89604990403669959779/20000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree083.table
  base := (1070560636233347542780837554846440518811/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-60417056308027284620906782921515000000000000)
      constant := (1526302038439808600089019178033604108251713808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree083.table
  base := (34257940359467117376170310521964093152071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (40018)
      previous := (0)
      next := (29920)
      square := (1361091865354477128333132723315000000000000)
      linear := (-133759925098017650050702398843990000000000000)
      constant := (3391503080873359255968275797923458852130433709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224012476009174899447/50000000000000000000)
  centralHi := (89604990403669959779/20000000000000000000)
  directionLo := (225374266521923111429/50000000000000000000)
  directionHi := (450748533043846222859/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree084.table
  base := (8924149623427561554250017433717938215313/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-61120508316450501331146272403870000000000000)
      constant := (1563007535780628250877101335720257631749494758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree084.table
  base := (35696598493710243566915819601069598415103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3638)
      previous := (0)
      next := (2720)
      square := (123735624123134284393921156665000000000000)
      linear := (-12301594386249469453060106459220000000000000)
      constant := (315732602736707754921194496946949113941964767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (225374266521923111429/50000000000000000000)
  centralHi := (450748533043846222859/100000000000000000000)
  directionLo := (453455755781436763747/100000000000000000000)
  directionHi := (113363938945359190937/25000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree085.table
  base := (74322299471411805409019349386479000511129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-247295841299494872165543047544900000000000000)
      constant := (6400605000164294015304508258777968958473584907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree085.table
  base := (74322299471411801891376804392423824441353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1870000000000000000000000000000000000000000
      center := (4708)
      previous := (0)
      next := (3520)
      square := (160128454747585544509780320390000000000000)
      linear := (-16102958988173020931367052148100000000000000)
      constant := (418304440953803227646110848272133255170533011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (453455755781436763747/100000000000000000000)
  centralHi := (113363938945359190937/25000000000000000000)
  directionLo := (45614691148954271059/10000000000000000000)
  directionHi := (456146911489542710591/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree086.table
  base := (19325797041581073987071502621639257942709/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-62527412333296934751625251368580000000000000)
      constant := (1637733181217840523307193745642075980648830047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree086.table
  base := (77303188166324293613778950811740454026547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-276865529100394383699157430932560000000000000)
      constant := (7278180869753399125367172269139202903350392913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45614691148954271059/10000000000000000000)
  centralHi := (456146911489542710591/100000000000000000000)
  directionLo := (458822282884760733633/100000000000000000000)
  directionHi := (229411141442380366817/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree087.table
  base := (40167931533847767989964023962632552599357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-126461728683440302923729481701870000000000000)
      constant := (3351506658615426028574999161237364649143946231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree087.table
  base := (16067172613539106886136752449009227720851/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-279980755401847411565074975347420000000000000)
      constant := (7447133380809617316216286107124071674622926645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (458822282884760733633/100000000000000000000)
  centralHi := (229411141442380366817/50000000000000000000)
  directionLo := (11537053612212860313/2500000000000000000)
  directionHi := (461482144488514412521/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree088.table
  base := (83420324171180160770155309311108752773681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-255737265400573472688416921333160000000000000)
      constant := (6856846777230236220540661269152566534246522323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree088.table
  base := (83420324171180159742078374552974478520241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7276)
      previous := (0)
      next := (5440)
      square := (247471248246268568787842313330000000000000)
      linear := (-25735998336663676311908410887480000000000000)
      constant := (692548457215408684406162276316529624292349649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11537053612212860313/2500000000000000000)
  centralHi := (461482144488514412521/100000000000000000000)
  directionLo := (18565070518233009239/4000000000000000000)
  directionHi := (3625990335592384617/781250000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree089.table
  base := (86556571472545673338647787109908990348153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-258551073434266339529374879262580000000000000)
      constant := (7012433104857312294606501240880777619173725099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree089.table
  base := (86556571472545672656447157441580319568347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-286211208004753467296910064177140000000000000)
      constant := (7790879815419578654503540877508013835907775113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18565070518233009239/4000000000000000000)
  centralHi := (3625990335592384617/781250000000000000)
  directionLo := (466756397387317525581/100000000000000000000)
  directionHi := (233378198693658762791/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree090.table
  base := (22436151241917109238905577195815373465219/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-65341220366989801592583209298000000000000000)
      constant := (1792443075025047958663888337807785721700226377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree090.table
  base := (89744604967668436502954928527326765103719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-289326434306206495162827608592000000000000000)
      constant := (7965673738946757653346968576405371786264722701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466756397387317525581/100000000000000000000)
  centralHi := (233378198693658762791/50000000000000000000)
  directionLo := (11734282490637267479/2500000000000000000)
  directionHi := (469371299625490699161/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree091.table
  base := (46492212326264922866944251274529724660097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (36146)
      previous := (0)
      next := (27280)
      square := (1234359184591682151929670223755000000000000)
      linear := (-132089344750826036605645397560710000000000000)
      constant := (3664432181473644599957523879177924196195059651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree091.table
  base := (92984424652529845433539167645598385452557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-292441660607659523028745153006860000000000000)
      constant := (8142414799938257377007077384570587267353678703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11734282490637267479/2500000000000000000)
  centralHi := (469371299625490699161/100000000000000000000)
  directionLo := (117992928634054394779/25000000000000000000)
  directionHi := (471971714536217579117/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree092.table
  base := (96276030523212663935315233997338481075887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-266992497535344940052248753050840000000000000)
      constant := (7489709293387310999751952401750966840941782221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree092.table
  base := (48138015261606331868019763559763975561333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (40018)
      previous := (0)
      next := (29920)
      square := (1361091865354477128333132723315000000000000)
      linear := (-147778443454556275447331348710860000000000000)
      constant := (4160551499190812466577454778369449678309477607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117992928634054394779/25000000000000000000)
  centralHi := (471971714536217579117/100000000000000000000)
  directionLo := (237278940138179744651/50000000000000000000)
  directionHi := (474557880276359489303/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree093.table
  base := (6226213910993595323474731541763743134871/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 232500000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (440)
      square := (19909019106317454063381777802500000000000)
      linear := (-2175857302976111345912957346615000000000000)
      constant := (61712153962977790329679925656908612446172012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree093.table
  base := (19923884515179505008677276363346065508917/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-298672113210565578760580241836580000000000000)
      constant := (8501738334264718556109550754614455711264235715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237278940138179744651/50000000000000000000)
  centralHi := (474557880276359489303/100000000000000000000)
  directionLo := (119282507137081461687/25000000000000000000)
  directionHi := (477130028548325846749/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree094.table
  base := (25753650201714895809373808353135312980297/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-68155028400682668433541167227420000000000000)
      constant := (1954164439250588867913958827929979107322196251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree094.table
  base := (103014600806859583149785117790498721735833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-301787339512018606626497786251440000000000000)
      constant := (8684320807575696959782779900460675436398213107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119282507137081461687/25000000000000000000)
  centralHi := (477130028548325846749/100000000000000000000)
  directionLo := (479688384842348385427/100000000000000000000)
  directionHi := (119922096210587096357/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree095.table
  base := (106461565212465306693916797262443969204751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-275433921636423540575122626839100000000000000)
      constant := (7982761290156163940974205275324375963217297133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree095.table
  base := (106461565212465306635730995978157141604709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (7276)
      previous := (0)
      next := (5440)
      square := (247471248246268568787842313330000000000000)
      linear := (-27718415073951966772037757333300000000000000)
      constant := (806259128936637195253817402617937413923760901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479688384842348385427/100000000000000000000)
  centralHi := (119922096210587096357/25000000000000000000)
  directionLo := (120558292166796748241/25000000000000000000)
  directionHi := (96446633733437398593/20000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree096.table
  base := (21992063157833882000163043272499509484897/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (72292)
      previous := (0)
      next := (54560)
      square := (2468718369183364303859340447510000000000000)
      linear := (-278247729670116407416080584768520000000000000)
      constant := (8150617690860450350611938418746840429224790255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree096.table
  base := (6872519736823088122638580733975427955279/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7947500000000000000000000000000000000000000
      center := (20009)
      previous := (0)
      next := (14960)
      square := (680545932677238564166566361657500000000000)
      linear := (-77004448028731165589583218770290000000000000)
      constant := (2263831791608846164352170740501551541879327764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120558292166796748241/25000000000000000000)
  centralHi := (96446633733437398593/20000000000000000000)
  directionLo := (48476459376993521277/10000000000000000000)
  directionHi := (484764593769935212771/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree097.table
  base := (7094428283344494634290063723428161126199/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-70265384425952318564259635674485000000000000)
      constant := (2080056739776309895271125904174221054107326868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree097.table
  base := (22702170506702382824607609731175538178989/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-311133018416377690224250419496020000000000000)
      constant := (9243751051961824215372125764593305179355030155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell213.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48476459376993521277/10000000000000000000)
  centralHi := (484764593769935212771/100000000000000000000)
  directionLo := (243641434172774172059/50000000000000000000)
  directionHi := (487282868345548344119/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree098.table
  base := (29278293860528832590446669974826507214179/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (18073)
      previous := (0)
      next := (13640)
      square := (617179592295841075964835111877500000000000)
      linear := (-70968836434375535274499125156840000000000000)
      constant := (2122897273720198583062956092208234820298478057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree098.table
  base := (117113175442115330344804394471288332260399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (80036)
      previous := (0)
      next := (59840)
      square := (2722183730708954256666265446630000000000000)
      linear := (-314248244717830718090167963910880000000000000)
      constant := (9434122074871590784871716611695945608255808421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell213.Kernel098
