import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell088.Parameters
import ForestUnimodality.BinomialMassData.Q10787_21012.Batch000_049
import ForestUnimodality.BinomialMassData.Q10787_21012.Batch050_099
import ForestUnimodality.BinomialMassData.Q10787_21012.Batch100_149
import ForestUnimodality.BinomialMassData.Q10787_21012.Batch150_199
import ForestUnimodality.BinomialMassData.Q53_103.Batch000_049
import ForestUnimodality.BinomialMassData.Q53_103.Batch050_099
import ForestUnimodality.BinomialMassData.Q53_103.Batch100_149
import ForestUnimodality.BinomialMassData.Q53_103.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree000.table
  base := (449708770334268272633693187/5000000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (9)
      square := (60213588985442205447906616000000000000)
      linear := (-1957655839094164362118588600000000000)
      constant := (89941754066853654526738637400000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree000.table
  base := (449708770334268272633693187/5000000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (9)
      square := (60213588985442205447906616000000000000)
      linear := (-1957655839094164362118588600000000000)
      constant := (89941754066853654526738637400000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree001.table
  base := (503959351693878536089473154641223536610791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-17599943178326041800482721962248854000000000000)
      constant := (13910915217856697272689344599307726691749996351119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree001.table
  base := (503045048122913829492460391888986719553871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-6781807353400079887979605399454000000000000)
      constant := (5338603183682850039069072048145374107747017439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9995757418433980889/20000000000000000000)
  directionHi := (24989393546084952223/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree002.table
  base := (37062160979172746462307167208010159883403/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-17329845314111707184203823997770367000000000000)
      constant := (4099809755568846144929515330819189862156245330508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree002.table
  base := (295541007563054474972367398315547296790491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-13355926998830659878782049734334000000000000)
      constant := (3142373884959361512051028623606749271650319019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9995757418433980889/20000000000000000000)
  centralHi := (24989393546084952223/50000000000000000000)
  directionLo := (17670169634176015221/25000000000000000000)
  directionHi := (14136135707340812177/20000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree003.table
  base := (185434617313185230440061118168569154156561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-5746604230902309659592508225425846000000000000)
      constant := (573014172318880549529276506746040955713170182561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree003.table
  base := (18467035252549455478234866586393179587689/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (190962)
      previous := (95481)
      next := (95481)
      square := (638805965546556357596841289144000000000000)
      linear := (-1993004664426123986958449406921400000000000)
      constant := (197471097267114982694280642899643442245792601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17670169634176015221/25000000000000000000)
  centralHi := (14136135707340812177/20000000000000000000)
  directionLo := (8656579854430586351/10000000000000000000)
  directionHi := (86565798544305863511/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree004.table
  base := (62069708309215773346093248909315965384399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-34389592764009079752128750031062247000000000000)
      constant := (1748338809948563008057827765784300125660794465591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree004.table
  base := (123581122102757011904094887148693728693769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-26504166289691819860386938404094000000000000)
      constant := (1338561993550790885837162022262227767712195321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8656579854430586351/10000000000000000000)
  centralHi := (86565798544305863511/100000000000000000000)
  directionLo := (99957574184339808891/100000000000000000000)
  directionHi := (24989393546084952223/25000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree005.table
  base := (88826148839846452916555046036971055560179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-85838932977915532072182426095416374000000000000)
      constant := (2561931398674943660194068716345223197367079367611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree005.table
  base := (88428405310888293642454988365775958959017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-33078285935122399851189382738974000000000000)
      constant := (980956286969521448191237661416887148596211353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99957574184339808891/100000000000000000000)
  centralHi := (24989393546084952223/25000000000000000000)
  directionLo := (111755965371080953601/100000000000000000000)
  directionHi := (55877982685540476801/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree006.table
  base := (33647516457636114894735255986314364594701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (275940090)
      previous := (137970045)
      next := (137970045)
      square := (923074620214773936727435662813080000000000000)
      linear := (-5716593357100716924450408451594903000000000000)
      constant := (112013778820898233975621103099813903661717860701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree006.table
  base := (67008564665725533963205075516685024624599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-39652405580552979841991827073854000000000000)
      constant := (772425462857857668247952055030395426242370791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111755965371080953601/100000000000000000000)
  centralHi := (55877982685540476801/50000000000000000000)
  directionLo := (24484505267802896177/20000000000000000000)
  directionHi := (61211263169507240443/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree007.table
  base := (10653288003602428083979396068116964301393/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (993384324)
      previous := (496692162)
      next := (496692162)
      square := (3323068632773186172218768386127088000000000000)
      linear := (-23991685575542055441606455632400026800000000000)
      constant := (337269469168054094435022376844959684085317154537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree007.table
  base := (26526589843315803272628693707147629422891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-23113262612991779916397135704367000000000000)
      constant := (323233924168360136433442572334268200547450619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24484505267802896177/20000000000000000000)
  centralHi := (61211263169507240443/50000000000000000000)
  directionLo := (33057860368631640473/25000000000000000000)
  directionHi := (132231441474526561893/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree008.table
  base := (43474906399030426652908791635931945297659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-137018175327607649775957204195292014000000000000)
      constant := (1482122143787183990187022758920317673931110124931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree008.table
  base := (1732361633420299893390447266632206493241/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (1277611931093112715193682578288000000000000)
      linear := (-10560128974282827964719343148722800000000000)
      constant := (113714028683283364390146880857215793433968845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33057860368631640473/25000000000000000000)
  centralHi := (132231441474526561893/100000000000000000000)
  directionLo := (17670169634176015221/12500000000000000000)
  directionHi := (141361357073408121769/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree009.table
  base := (18098590022528161444220603061233735298219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (275940090)
      previous := (137970045)
      next := (137970045)
      square := (923074620214773936727435662813080000000000000)
      linear := (-8559884598750279019104562790476883000000000000)
      constant := (75334498947413730010657536167765279408074752219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree009.table
  base := (563474468463098325704074580358422490323/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-29687382258422359907199580039247000000000000)
      constant := (260275416736096399159784835178573134394774624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17670169634176015221/12500000000000000000)
  centralHi := (141361357073408121769/100000000000000000000)
  directionLo := (18742045159563714167/12500000000000000000)
  directionHi := (149936361276509713337/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree010.table
  base := (30503425039111253870032148357508398918881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-171137670227402394911807056261875774000000000000)
      constant := (1282385956977429863755558742599096842343192583929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree010.table
  base := (237419664552125799172169318042076496089/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-32974442081137649902600802206687000000000000)
      constant := (246306582050278496332947945817306931008524864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18742045159563714167/12500000000000000000)
  centralHi := (149936361276509713337/100000000000000000000)
  directionLo := (158046801903880644537/100000000000000000000)
  directionHi := (79023400951940322269/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree011.table
  base := (646883169587577879224424488625013694183/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27594009000000000000000000000000000000000000000
      center := (496692162)
      previous := (248346081)
      next := (248346081)
      square := (1661534316386593086109384193063544000000000000)
      linear := (-18819741767729976747973198229516765400000000000)
      constant := (124691469388558485204357637237821483659635798588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree011.table
  base := (25776793378251079175046258254734337858919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-72523003807705879796004048748254000000000000)
      constant := (479300919171413011400709663149130590345271671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158046801903880644537/100000000000000000000)
  centralHi := (79023400951940322269/50000000000000000000)
  directionLo := (165760884261785173367/100000000000000000000)
  directionHi := (20720110532723146671/12500000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree012.table
  base := (22010777003745152849635055377820491652461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-22806351680799682227517434258717726000000000000)
      constant := (137918979259194460730559464508951827226937078461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree012.table
  base := (2740485603558747908109474492462308100841/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-39548561726568229893403246541567000000000000)
      constant := (238717237117433080497984154799854506567288676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165760884261785173367/100000000000000000000)
  centralHi := (20720110532723146671/12500000000000000000)
  directionLo := (173131597088611727021/100000000000000000000)
  directionHi := (86565798544305863511/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree013.table
  base := (9361765943307424348199617568800901874669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-111158456288547256307790917180875707000000000000)
      constant := (630157550930334630352903892879641010287733258021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree013.table
  base := (18646129522353040790348120737841764389217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-85671243098567039777608937418014000000000000)
      constant := (485052629489554457492024678220885278405203153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173131597088611727021/100000000000000000000)
  centralHi := (86565798544305863511/50000000000000000000)
  directionLo := (2815641867911193181/1562500000000000000)
  directionHi := (36040215909263272717/20000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree014.table
  base := (317825816427860888058822214751470367883/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27594009000000000000000000000000000000000000000
      center := (496692162)
      previous := (248346081)
      next := (248346081)
      square := (1661534316386593086109384193063544000000000000)
      linear := (-23937666002699188518350676039504329400000000000)
      constant := (130067279531645224365864333821233075572984064735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree014.table
  base := (15822000785681702701542693137403164816619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-92245362743997619768411381752894000000000000)
      constant := (500866108448693314018271765332386175539510971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2815641867911193181/1562500000000000000)
  centralHi := (36040215909263272717/20000000000000000000)
  directionLo := (187003497905419637467/100000000000000000000)
  directionHi := (46750874476354909367/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree015.table
  base := (6714261815970154188881979924854292494651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (275940090)
      previous := (137970045)
      next := (137970045)
      square := (923074620214773936727435662813080000000000000)
      linear := (-14246467082049403208412871468240843000000000000)
      constant := (75554654069440890824605386586090736892892460651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree015.table
  base := (13366392568459506186279630954180956687077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-98819482389428199759213826087774000000000000)
      constant := (523972021027870256600293200842015769493199893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187003497905419637467/100000000000000000000)
  centralHi := (46750874476354909367/25000000000000000000)
  directionLo := (193567010071620251263/100000000000000000000)
  directionHi := (1512242266184533213/781250000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree016.table
  base := (1408999671893878141939707762454073497793/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-136748077463393315159678306230813527000000000000)
      constant := (718251592629983896302639028504809276739046088548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree016.table
  base := (11216301709409366325639495742738506960863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-105393602034858779750016270422654000000000000)
      constant := (553701966689096691333272662282136820347795567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193567010071620251263/100000000000000000000)
  centralHi := (1512242266184533213/781250000000000000)
  directionLo := (99957574184339808891/50000000000000000000)
  directionHi := (199915148368679617783/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree017.table
  base := (2343215261882160156671164626127800093873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 477405000000000000000000000000000000000000000
      center := (8593290)
      previous := (4296645)
      next := (4296645)
      square := (28746268449595036091857858011480000000000000)
      linear := (-502691872624020766240971519887403000000000000)
      constant := (2645126360409004451616630908930666711526175826) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree017.table
  base := (9323002820286214430819585674580487190989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-111967721680289359740818714757534000000000000)
      constant := (589539017788480684497702285954242388609202301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99957574184339808891/50000000000000000000)
  centralHi := (199915148368679617783/100000000000000000000)
  directionLo := (20606781822127305159/10000000000000000000)
  directionHi := (206067818221273051591/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree018.table
  base := (480759417756108466004562450838958002603/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (275940090)
      previous := (137970045)
      next := (137970045)
      square := (923074620214773936727435662813080000000000000)
      linear := (-17089758323698965303067025807122823000000000000)
      constant := (90891564134391053808922197927371575099510404824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree018.table
  base := (7647603992583101480576365921777002846553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-118541841325719939731621159092414000000000000)
      constant := (631070570068672013927209410868824223199080777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20606781822127305159/10000000000000000000)
  centralHi := (206067818221273051591/100000000000000000000)
  directionLo := (212042035610112182653/100000000000000000000)
  directionHi := (106021017805056091327/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree019.table
  base := (1239621286939452353622842046420151687679/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (993384324)
      previous := (496692162)
      next := (496692162)
      square := (3323068632773186172218768386127088000000000000)
      linear := (-64935079455295749604626278112300538800000000000)
      constant := (351424431595337674641570315497560905151179515111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree019.table
  base := (6158391330311635222369836211764635599023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-125115960971150519722423603427294000000000000)
      constant := (677960170807129826214597174134257019070035007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212042035610112182653/100000000000000000000)
  centralHi := (106021017805056091327/50000000000000000000)
  directionLo := (108926241127751824209/50000000000000000000)
  directionHi := (217852482255503648419/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree020.table
  base := (972894502530509517187404958362467521877/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (993384324)
      previous := (496692162)
      next := (496692162)
      square := (3323068632773186172218768386127088000000000000)
      linear := (-68347028945275224118211263318958914800000000000)
      constant := (378276108915109961674867036537901100060881634893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree020.table
  base := (482914320633100622520133204649789057403/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (190962)
      previous := (95481)
      next := (95481)
      square := (638805965546556357596841289144000000000000)
      linear := (-13169008061658109971322604776217400000000000)
      constant := (72992963476151727410640074409077612109988427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108926241127751824209/50000000000000000000)
  centralHi := (217852482255503648419/100000000000000000000)
  directionLo := (223511930742161907203/100000000000000000000)
  directionHi := (55877982685540476801/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree021.table
  base := (733869773152189859556303548778462311581/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (110376036)
      previous := (55188018)
      next := (55188018)
      square := (369229848085909574690974265125232000000000000)
      linear := (-7973219826139410959088472058401921200000000000)
      constant := (45293755643956512364741211064581824925769657581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree021.table
  base := (1818994492182399941455388037400824230677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-69132100131005839852014246048527000000000000)
      constant := (393373468175788937522933930059882344263252293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223511930742161907203/100000000000000000000)
  centralHi := (55877982685540476801/25000000000000000000)
  directionLo := (114515787495975233007/50000000000000000000)
  directionHi := (45806314998390093203/20000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree022.table
  base := (1297183628621831704792099242035410171831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-187927319813085432863453084330689167000000000000)
      constant := (1098565341446589841350245058416098218100196160479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree022.table
  base := (160411767052053934552626279152212075221/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-72419159953721129847415468215967000000000000)
      constant := (424108751181518891640829724945100543248156712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114515787495975233007/50000000000000000000)
  centralHi := (45806314998390093203/20000000000000000000)
  directionLo := (23442129063397351571/10000000000000000000)
  directionHi := (234421290633973515711/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree023.table
  base := (406017339819500323145909569480813804407/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-196457193538034119147415547347335107000000000000)
      constant := (1183844512041947733404750758058488590142261995326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree023.table
  base := (319902040704379828260563118851557014607/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (1277611931093112715193682578288000000000000)
      linear := (-30282487910574567937126676153362800000000000)
      constant := (182835525343004427686798887421548568367965663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23442129063397351571/10000000000000000000)
  centralHi := (234421290633973515711/100000000000000000000)
  directionLo := (239689842633563277601/100000000000000000000)
  directionHi := (119844921316781638801/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree024.table
  base := (745418878236508331130352065842143049269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-45552681613996178984750668969773566000000000000)
      constant := (283281589327389753714340584908927800431201803269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree024.table
  base := (723745785643807182109303321819727880253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-157986559198303419676435825101694000000000000)
      constant := (984489297024259974169928270802801493081604077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239689842633563277601/100000000000000000000)
  centralHi := (119844921316781638801/50000000000000000000)
  directionLo := (244845052678028961771/100000000000000000000)
  directionHi := (61211263169507240443/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree025.table
  base := (-26295850294238778295114247393828478393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-213516940987931491715340473380626987000000000000)
      constant := (1371181390510552886352315712922539114172767252463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree025.table
  base := (-17921382704537593333417784163053261331/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-82280339421866999833619134718287000000000000)
      constant := (529518010317811861448657476926553335901078842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244845052678028961771/100000000000000000000)
  centralHi := (61211263169507240443/25000000000000000000)
  directionLo := (62473483865212380557/25000000000000000000)
  directionHi := (249893935460849522229/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree026.table
  base := (-389631939447956650083891597015942659599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-222046814712880177999302936397272927000000000000)
      constant := (1472958894793047450915245005338484549607541257609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree026.table
  base := (-796058935080329684828235365200805919969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-171134798489164579658040713771454000000000000)
      constant := (1137719397066717062116813714719548649995048879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62473483865212380557/25000000000000000000)
  centralHi := (249893935460849522229/100000000000000000000)
  directionLo := (254842810648673539091/100000000000000000000)
  directionHi := (63710702662168384773/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree027.table
  base := (-288492229161892277069190272714326828277/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (110376036)
      previous := (55188018)
      next := (55188018)
      square := (369229848085909574690974265125232000000000000)
      linear := (-10247852819459060634811795529507505200000000000)
      constant := (70221829876707231690268192516996906130175889723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree027.table
  base := (-1457212570610697488758022671186636039059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-177708918134595159648843158106334000000000000)
      constant := (1220456271453488332722130587644338978261623069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254842810648673539091/100000000000000000000)
  centralHi := (63710702662168384773/25000000000000000000)
  directionLo := (64924348908229397633/25000000000000000000)
  directionHi := (259697395632917590533/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree028.table
  base := (-2048833126933621469005644765311131722429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-478213124325555101134455724861129614000000000000)
      constant := (3384372955789520151426898592522562125451108672139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree028.table
  base := (-515442985949256575465372671062249793961/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-92141518890012869819822801220607000000000000)
      constant := (653588176899334828041593637817317183871735502) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64924348908229397633/25000000000000000000)
  centralHi := (259697395632917590533/100000000000000000000)
  directionLo := (52892576589810624757/20000000000000000000)
  directionHi := (132231441474526561893/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree029.table
  base := (-1302001949476920093911092469497771307229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-247636435887726236851190325447210747000000000000)
      constant := (1809467216388252086631770622902225609818381208939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree029.table
  base := (-2615338426356390886744056825834803167301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-190857157425456319630448046776094000000000000)
      constant := (1397820219149714586043502905266304573198103691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52892576589810624757/20000000000000000000)
  centralHi := (132231441474526561893/50000000000000000000)
  directionLo := (134572002676010791513/50000000000000000000)
  directionHi := (269144005352021583027/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree030.table
  base := (-77818265810789661617758368160350068113/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3066001000000000000000000000000000000000000000
      center := (55188018)
      previous := (27594009)
      next := (27594009)
      square := (184614924042954787345487132562616000000000000)
      linear := (-5692584658059442736336728632530148600000000000)
      constant := (42928172288949886478442959455792589623261895548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree030.table
  base := (-390331001971242864563001594857572679473/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-98715638535443449810625245555487000000000000)
      constant := (746168811654672792251588850143734045773883772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134572002676010791513/50000000000000000000)
  centralHi := (269144005352021583027/100000000000000000000)
  directionLo := (6843627271782371093/2500000000000000000)
  directionHi := (273745090871294843721/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree031.table
  base := (-1789518730330997876954532441199821391279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-264696183337623609419115251480502627000000000000)
      constant := (2059032566753056906717692330506802730980654752489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree031.table
  base := (-896926315249039144954632531532599886529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-102002698358158739806026467722927000000000000)
      constant := (795343041008831099397267773369808295607627678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6843627271782371093/2500000000000000000)
  centralHi := (273745090871294843721/100000000000000000000)
  directionLo := (69567527417313173037/25000000000000000000)
  directionHi := (278270109669252692149/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree032.table
  base := (-4006328557280717443764143014029393411149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-546452114125144591406155428994297134000000000000)
      constant := (4382429380480436592447238569319679119948213793659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree032.table
  base := (-4013896347882284285557559897592148104527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-210579516361748059602855379780734000000000000)
      constant := (1692829671229010928111875134782572900759073057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69567527417313173037/25000000000000000000)
  centralHi := (278270109669252692149/100000000000000000000)
  directionLo := (282722714146816243537/100000000000000000000)
  directionHi := (141361357073408121769/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree033.table
  base := (-87949674198983328811545303197333592657/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3066001000000000000000000000000000000000000000
      center := (55188018)
      previous := (27594009)
      next := (27594009)
      square := (184614924042954787345487132562616000000000000)
      linear := (-6261242906389355155267559500306544600000000000)
      constant := (51739430911575677202424499097068561587900226715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree033.table
  base := (-440408464310466937442487008603908470023/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (190962)
      previous := (95481)
      next := (95481)
      square := (638805965546556357596841289144000000000000)
      linear := (-21715363600717863959365782411561400000000000)
      constant := (179873801348632244595367018956861335041525993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282722714146816243537/100000000000000000000)
  centralHi := (141361357073408121769/50000000000000000000)
  directionLo := (287106273448956212003/100000000000000000000)
  directionHi := (71776568362239053001/25000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree034.table
  base := (-1188734782343989434419453853081668567249/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 477405000000000000000000000000000000000000000
      center := (8593290)
      previous := (4296645)
      next := (4296645)
      square := (28746268449595036091857858011480000000000000)
      linear := (-1004449150562178782944645814984223000000000000)
      constant := (8547328915865082114610411322928232907060996462) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree034.table
  base := (-1190172861516814686268641005511083549189/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-111863877826304609792230134225247000000000000)
      constant := (954192710612110139836049664431843829253307798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287106273448956212003/100000000000000000000)
  centralHi := (71776568362239053001/25000000000000000000)
  directionLo := (291423903297157949159/100000000000000000000)
  directionHi := (7285597582428948729/2500000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree035.table
  base := (-1270188947438681085803742788617077235143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-298815678237418354554965103547086387000000000000)
      constant := (2616897251962304128778755786508999372689537883426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree035.table
  base := (-254288212666644494058379702378168030223/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (190962)
      previous := (95481)
      next := (95481)
      square := (638805965546556357596841289144000000000000)
      linear := (-23030187529803979957526271278537400000000000)
      constant := (202175017255166928640300350927199030734728386) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291423903297157949159/100000000000000000000)
  centralHi := (7285597582428948729/2500000000000000000)
  directionLo := (147839245949913209137/50000000000000000000)
  directionHi := (11827139675993056731/4000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree036.table
  base := (-537667723221684429109608636300798799669/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3066001000000000000000000000000000000000000000
      center := (55188018)
      previous := (27594009)
      next := (27594009)
      square := (184614924042954787345487132562616000000000000)
      linear := (-6829901154719267574198390368082940600000000000)
      constant := (61520176026843469094513828589254585179416046331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree036.table
  base := (-2690517237008240767747080969534635350589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-118437997471735189783032578560127000000000000)
      constant := (1069406949474684646549015740073459053565601299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147839245949913209137/50000000000000000000)
  centralHi := (11827139675993056731/4000000000000000000)
  directionLo := (299872722553019426673/100000000000000000000)
  directionHi := (149936361276509713337/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree037.table
  base := (-5644178459873164836931068937993547185901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-631750851374631454245780059160756534000000000000)
      constant := (5849379427594813597922091645614169302510323132891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree037.table
  base := (-5647966230050850097969677803518227312917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-243450114588900959556867601455134000000000000)
      constant := (2259561067547735050676570655663773126437263547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299872722553019426673/100000000000000000000)
  centralHi := (149936361276509713337/50000000000000000000)
  directionLo := (152004546717001704749/50000000000000000000)
  directionHi := (304009093434003409499/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree038.table
  base := (-5884507299377357289521350321750164547097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-648810598824528826813704985194048414000000000000)
      constant := (6171450826921400549826944312329364710735924458127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree038.table
  base := (-5887797620322753653590173998598725919281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-250024234234331539547670045790014000000000000)
      constant := (2383978543355676942614898128539838116722347871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152004546717001704749/50000000000000000000)
  centralHi := (304009093434003409499/100000000000000000000)
  directionLo := (308089935002377291231/100000000000000000000)
  directionHi := (9627810468824290351/3125000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree039.table
  base := (-7623399238436727277760641540485344277/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3066001000000000000000000000000000000000000000
      center := (55188018)
      previous := (27594009)
      next := (27594009)
      square := (184614924042954787345487132562616000000000000)
      linear := (-7398559403049179993129221235859336600000000000)
      constant := (72255565678394017033533037550896834166909897840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree039.table
  base := (-381348475839715721929610189030011878061/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-128299176939881059769236245062447000000000000)
      constant := (1256027609541641495242292621630407831885206808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308089935002377291231/100000000000000000000)
  centralHi := (9627810468824290351/3125000000000000000)
  directionLo := (156058712676490376923/50000000000000000000)
  directionHi := (312117425352980753847/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree040.table
  base := (-157192694688579202323077763667715153953/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27594009000000000000000000000000000000000000000
      center := (496692162)
      previous := (248346081)
      next := (248346081)
      square := (1661534316386593086109384193063544000000000000)
      linear := (-68293009372432357194955483726063217400000000000)
      constant := (684400503706919193052887624991080526129538129692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree040.table
  base := (-1258037110671398706280362305250437132979/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (1277611931093112715193682578288000000000000)
      linear := (-52634494705038539905854986891954800000000000)
      constant := (528756340423279230915439056217790112456225789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156058712676490376923/50000000000000000000)
  centralHi := (312117425352980753847/100000000000000000000)
  directionLo := (158046801903880644537/50000000000000000000)
  directionHi := (12643744152310451563/4000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree041.table
  base := (-6452227997816723073520372783117580939451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-699989841174220944517479763293924054000000000000)
      constant := (7194442357466439525456216945697653734998560650941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree041.table
  base := (-1613594027480332630263651921871428261059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-134873296585311639760038689397327000000000000)
      constant := (1389575024908374024760032132342369035156850138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158046801903880644537/50000000000000000000)
  centralHi := (12643744152310451563/4000000000000000000)
  directionLo := (160010191493684560211/50000000000000000000)
  directionHi := (320020382987369120423/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree042.table
  base := (-3296459584136218080878985708268323005183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (275940090)
      previous := (137970045)
      next := (137970045)
      square := (923074620214773936727435662813080000000000000)
      linear := (-39836088256895462060300260518178663000000000000)
      constant := (419683068645963681357598094469068601897785916817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree042.table
  base := (-659478037754019931246586835512588383403/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (190962)
      previous := (95481)
      next := (95481)
      square := (638805965546556357596841289144000000000000)
      linear := (-27632071281605385951087982312953400000000000)
      constant := (291815354568572455968014109201893749840477573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160010191493684560211/50000000000000000000)
  centralHi := (320020382987369120423/100000000000000000000)
  directionLo := (161949779782643468259/50000000000000000000)
  directionHi := (323899559565286936519/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree043.table
  base := (-671032200566573144302487387424193683361/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27594009000000000000000000000000000000000000000
      center := (496692162)
      previous := (248346081)
      next := (248346081)
      square := (1661534316386593086109384193063544000000000000)
      linear := (-73410933607401568965332961536050781400000000000)
      constant := (792354875128483661445948257845858403133593415751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree043.table
  base := (-6711933716816194148387572209727574841151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-282894832461484439501682267464414000000000000)
      constant := (3060786510082692762736070021269542158510229041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161949779782643468259/50000000000000000000)
  centralHi := (323899559565286936519/100000000000000000000)
  directionLo := (32773282387608249647/10000000000000000000)
  directionHi := (327732823876082496471/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree044.table
  base := (-3402446969016474640781818182170659122419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-375584541761956531110627270696899847000000000000)
      constant := (4151095141082779473593197602777083515640038012229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree044.table
  base := (-6806288841899665903557334321789453153069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-289468952106915019492484711799294000000000000)
      constant := (3207044140163231586257759694153631691499090979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32773282387608249647/10000000000000000000)
  centralHi := (327732823876082496471/100000000000000000000)
  directionLo := (66304353704714069347/20000000000000000000)
  directionHi := (20720110532723146671/6250000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree045.table
  base := (-6877021940865627322769806443055421672323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-85358758997090048309908829714121286000000000000)
      constant := (965578794451590777045180003767078191597236009677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree045.table
  base := (-1375645715757106214505165755302086608179/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (1277611931093112715193682578288000000000000)
      linear := (-59208614350469119896657431226834800000000000)
      constant := (671384474905272192230904401860266163173828989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66304353704714069347/20000000000000000000)
  centralHi := (20720110532723146671/6250000000000000000)
  directionLo := (67053579222648572161/20000000000000000000)
  directionHi := (167633948056621430403/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree046.table
  base := (-6927033387871100850065389401289706544887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-785288578423707807357104393460383454000000000000)
      constant := (9087596321428084179943392698711901244993029218017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree046.table
  base := (-1385615330819453671155996425289596913037/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (1277611931093112715193682578288000000000000)
      linear := (-60523438279555235894817920093810800000000000)
      constant := (702083555751266480378578232583311466349590467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67053579222648572161/20000000000000000000)
  centralHi := (167633948056621430403/50000000000000000000)
  directionLo := (338972626215458077103/100000000000000000000)
  directionHi := (21185789138466129819/6250000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree047.table
  base := (-434700326910258764383430613367919316243/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-401174162936802589962514659746837667000000000000)
      constant := (4747172077027134684832743840290006737860534494504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree047.table
  base := (-6956106818396545255139016680122921888453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-309191311043206759464892044803934000000000000)
      constant := (3667527448633437177946067025528213921685402123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338972626215458077103/100000000000000000000)
  centralHi := (21185789138466129819/6250000000000000000)
  directionLo := (42829662706362366041/12500000000000000000)
  directionHi := (342637301650898928329/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree048.table
  base := (-6961771764073813459144497629985386783673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-91045341480389172499217138391885246000000000000)
      constant := (1101160686977885822680564796506198942135871798327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree048.table
  base := (-1392510112223972248544009376490777484049/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (1277611931093112715193682578288000000000000)
      linear := (-63153086137727467891138897827762800000000000)
      constant := (765649785657248693282871825998031741671724159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42829662706362366041/12500000000000000000)
  centralHi := (342637301650898928329/100000000000000000000)
  directionLo := (346263194177223454043/100000000000000000000)
  directionHi := (86565798544305863511/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree049.table
  base := (-6946931196907899832737719123644751340809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-836467820773399925060879171560259094000000000000)
      constant := (10335896938300845744868178589721291422198954386719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree049.table
  base := (-1389520726910727310045136436368267781071/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (1277611931093112715193682578288000000000000)
      linear := (-64467910066813583889299386694738800000000000)
      constant := (798516028195748927011926898532862247110617761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346263194177223454043/100000000000000000000)
  centralHi := (86565798544305863511/25000000000000000000)
  directionLo := (349851509645189331119/100000000000000000000)
  directionHi := (4373143870564866639/1250000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree050.table
  base := (-6910851208881433869173650770298120337467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-853527568223297297628804097593550974000000000000)
      constant := (10770691793595564211062621771601541059724852564797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree050.table
  base := (-345571578534842505566842204631231443899/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (190962)
      previous := (95481)
      next := (95481)
      square := (638805965546556357596841289144000000000000)
      linear := (-32891366997949849943729937780857400000000000)
      constant := (416051933058196351637447221720504531223351018) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349851509645189331119/100000000000000000000)
  centralHi := (4373143870564866639/1250000000000000000)
  directionLo := (176701696341760152211/50000000000000000000)
  directionHi := (353403392683520304423/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree051.table
  base := (-3426836826522756397420033817559930689133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-167356269833370755516480012231227000000000000)
      constant := (2155868288041283957782313227904294945318988003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree051.table
  base := (-1713543586619837213611634332134678956619/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-167743894812464539714050911071727000000000000)
      constant := (2166032506040325682147775458302173381898458058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176701696341760152211/50000000000000000000)
  centralHi := (353403392683520304423/100000000000000000000)
  directionLo := (178459965482056298143/50000000000000000000)
  directionHi := (356919930964112596287/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree052.table
  base := (-338775926672581884535139791593648083789/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27594009000000000000000000000000000000000000000
      center := (496692162)
      previous := (248346081)
      next := (248346081)
      square := (1661534316386593086109384193063544000000000000)
      linear := (-88764706312309204276465394966013473400000000000)
      constant := (1166829874929355339953941277511548426666187159798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree052.table
  base := (-338797516440214450034687880026914785757/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (190962)
      previous := (95481)
      next := (95481)
      square := (638805965546556357596841289144000000000000)
      linear := (-34206190927035965941890426647833400000000000)
      constant := (450721592972033259447280698536469722075807974) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178459965482056298143/50000000000000000000)
  centralHi := (356919930964112596287/100000000000000000000)
  directionLo := (2815641867911193181/781250000000000000)
  directionHi := (360402159092632727169/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree053.table
  base := (-3338243685141255056659112420957510221241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-452353405286494707666289437846713307000000000000)
      constant := (6065552368477555908067074420958740009087483854831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree053.table
  base := (-3338429805294198292429861305440411217491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-174318014457895119704853355406607000000000000)
      constant := (2342985510807626830201623242441423677393637981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2815641867911193181/781250000000000000)
  centralHi := (360402159092632727169/100000000000000000000)
  directionLo := (363851062163951638769/100000000000000000000)
  directionHi := (36385106216395163877/10000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree054.table
  base := (-6556666046703016098230238265019145056883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-102418506446987420877833755747413166000000000000)
      constant := (1400360269723845509379892152001893115236451665117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree054.table
  base := (-3278493415905942246282427662162786385001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-177605074280610409700254577574047000000000000)
      constant := (2434164694909932241791661173962832999241524391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363851062163951638769/100000000000000000000)
  centralHi := (36385106216395163877/10000000000000000000)
  directionLo := (367267579017043442657/100000000000000000000)
  directionHi := (183633789508521721329/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree055.table
  base := (-320806360862672721902470359565181568597/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27594009000000000000000000000000000000000000000
      center := (496692162)
      previous := (248346081)
      next := (248346081)
      square := (1661534316386593086109384193063544000000000000)
      linear := (-93882630547278416046842872776001037400000000000)
      constant := (1308470981614200780864806912125829425669000529254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree055.table
  base := (-401025222817330581656083339842584187211/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-180892134103325699695655799741487000000000000)
      constant := (2527145137510212376703647848654915194863028008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367267579017043442657/100000000000000000000)
  centralHi := (183633789508521721329/50000000000000000000)
  directionLo := (185326302609913346521/50000000000000000000)
  directionHi := (370652605219826693043/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree056.table
  base := (-1250986469062690783422832232394099922937/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (993384324)
      previous := (496692162)
      next := (496692162)
      square := (3323068632773186172218768386127088000000000000)
      linear := (-191177210584536306607270730758660450800000000000)
      constant := (2715101041363251168345914883567090851979577115567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree056.table
  base := (-6255170332904217291288939624845793370683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-368358387852081979382114043817854000000000000)
      constant := (5243853035133523967013687950641594978130424053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185326302609913346521/50000000000000000000)
  centralHi := (370652605219826693043/100000000000000000000)
  directionLo := (74801399162167854987/20000000000000000000)
  directionHi := (46750874476354909367/12500000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree057.table
  base := (-6073133426764781303379773134648319521181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-108105088930286545067142064425177126000000000000)
      constant := (1563958573862502694281409616017584297199739532819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree057.table
  base := (-6073338313609177790059604337298541239993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-374932507497512559372916488152734000000000000)
      constant := (5437017127208402276781339765767577775984914263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74801399162167854987/20000000000000000000)
  centralHi := (46750874476354909367/12500000000000000000)
  directionLo := (377331567821529604927/100000000000000000000)
  directionHi := (5895805747211400077/1562500000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree058.table
  base := (-5870774448182764695277865748321814340559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-990005547822476278172203505859886014000000000000)
      constant := (14585074476214857546331330419241959297190285888969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree058.table
  base := (-5870950783843886158685153131443287223031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-381506627142943139363718932487614000000000000)
      constant := (5633782092123061634499764509357770165850864121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377331567821529604927/100000000000000000000)
  centralHi := (5895805747211400077/1562500000000000000)
  directionLo := (380627102600245802643/100000000000000000000)
  directionHi := (95156775650061450661/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree059.table
  base := (-705986577555331677792196187222787185687/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-503532647636186825370064215946588947000000000000)
      constant := (7551923057188014603624617625225555085822273003268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree059.table
  base := (-5648044338444335190717382508776889062031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-388080746788373719354521376822494000000000000)
      constant := (5834147541642886992622171172327791983940913121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380627102600245802643/100000000000000000000)
  centralHi := (95156775650061450661/25000000000000000000)
  directionLo := (383894347956651341617/100000000000000000000)
  directionHi := (191947173978325670809/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree060.table
  base := (-5404519422330208290249978991778023415061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-113791671413585669256450373102941086000000000000)
      constant := (1736882356735571293171368191325784498431399558939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree060.table
  base := (-5404649921967438067590064466915143826491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-394654866433804299345323821157374000000000000)
      constant := (6038113147477074059206728867554937239144756981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383894347956651341617/100000000000000000000)
  centralHi := (191947173978325670809/50000000000000000000)
  directionLo := (387134020143240502527/100000000000000000000)
  directionHi := (1512242266184533213/390625000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree061.table
  base := (-1285170370854652223457328412426302011253/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-520592395086084197937989141979880827000000000000)
      constant := (8084679515065256428156322954849008141679533233446) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree061.table
  base := (-2570396850492647079804059495092748957139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-200614493039617439668063132746127000000000000)
      constant := (3122839316012229716016936349462738026313712349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387134020143240502527/100000000000000000000)
  centralHi := (1512242266184533213/390625000000000000)
  directionLo := (390346805688827678171/100000000000000000000)
  directionHi := (97586701422206919543/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree062.table
  base := (-971280266193402814319263728016706930223/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (993384324)
      previous := (496692162)
      next := (496692162)
      square := (3323068632773186172218768386127088000000000000)
      linear := (-211648907524413153688780641998610706800000000000)
      constant := (3343219790257950177247532164976427781417064165993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree062.table
  base := (-4856497801719577549582076926188578108337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-407803105724665459326928709827134000000000000)
      constant := (6456843760547957370759065744677213374848652767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390346805688827678171/100000000000000000000)
  centralHi := (97586701422206919543/25000000000000000000)
  directionLo := (98383340774326422947/25000000000000000000)
  directionHi := (393533363097305691789/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree063.table
  base := (-4551698021783457232211245253423400616441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-119478253896884793445758681780705046000000000000)
      constant := (1919128938693791482574054090603535870786591277559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree063.table
  base := (-2275890466901868953303050597239219623307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-207188612685048019658865577081007000000000000)
      constant := (3335804167278533303921444015198300119016336037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98383340774326422947/25000000000000000000)
  centralHi := (393533363097305691789/100000000000000000000)
  directionLo := (396694324423579685677/100000000000000000000)
  directionHi := (198347162211789842839/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree064.table
  base := (-4226587676769301065251357300288019017443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-1092364032521860513579753062059637294000000000000)
      constant := (17837543076153332936930664657563012476640506701013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree064.table
  base := (-2113329458875848278824670511475619097623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-210475672507763309654266799248447000000000000)
      constant := (3444986093105977475963761925962443156993317593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396694324423579685677/100000000000000000000)
  centralHi := (198347162211789842839/50000000000000000000)
  directionLo := (99957574184339808891/25000000000000000000)
  directionHi := (79966059347471847113/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree065.table
  base := (-3881083933133780591129856826729403447231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-1109423779971757886147677988092929174000000000000)
      constant := (18412246458712105301493797270298130148212476760921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree065.table
  base := (-242571570687380460425629691457509362459/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-213762732330478599649668021415887000000000000)
      constant := (3555967586795709186174377285523023265389379752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99957574184339808891/25000000000000000000)
  centralHi := (79966059347471847113/20000000000000000000)
  directionLo := (402941863484410351761/100000000000000000000)
  directionHi := (201470931742205175881/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree066.table
  base := (-351519832695872225450217973171230008137/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3066001000000000000000000000000000000000000000
      center := (55188018)
      previous := (27594009)
      next := (27594009)
      square := (184614924042954787345487132562616000000000000)
      linear := (-12516483638018391763506699045846900600000000000)
      constant := (211069669751041052146729161706024661723821949863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree066.table
  base := (-439406360635045243757522191956038009157/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-217049792153193889645069243583327000000000000)
      constant := (3668748588345678022456367287079715571043413548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402941863484410351761/100000000000000000000)
  centralHi := (201470931742205175881/50000000000000000000)
  directionLo := (406029585753912318863/100000000000000000000)
  directionHi := (25376849109619519929/6250000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree067.table
  base := (-1564470308420307747682614406838966527767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-571771637435776315641763920079756467000000000000)
      constant := (9794807131759650877545233505751484186332098652097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree067.table
  base := (-312898574459258606843756696355472055397/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (190962)
      previous := (95481)
      next := (95481)
      square := (638805965546556357596841289144000000000000)
      linear := (-44067370395181835928094093150153400000000000)
      constant := (756665809404098952596061258364796596964293227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406029585753912318863/100000000000000000000)
  centralHi := (25376849109619519929/6250000000000000000)
  directionLo := (409094003459715951053/100000000000000000000)
  directionHi := (204547001729857975527/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree068.table
  base := (-340289882210634490313564271876690749413/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 477405000000000000000000000000000000000000000
      center := (8593290)
      previous := (4296645)
      next := (4296645)
      square := (28746268449595036091857858011480000000000000)
      linear := (-2007963706438494816351994405177863000000000000)
      constant := (34934737350697208712610460939981855762221189388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree068.table
  base := (-2722357796899815365047980332418813568781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-447247823597248939271743375836414000000000000)
      constant := (7799417839841462940174679835833760806848802371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409094003459715951053/100000000000000000000)
  centralHi := (204547001729857975527/50000000000000000000)
  directionLo := (20606781822127305159/5000000000000000000)
  directionHi := (412135636442546103181/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree069.table
  base := (-1147670316165526460425516774643630873657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (275940090)
      previous := (137970045)
      next := (137970045)
      square := (923074620214773936727435662813080000000000000)
      linear := (-65425709431741520912187649568116483000000000000)
      constant := (1155792325581123806706820194512821793847736764343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree069.table
  base := (-2295373880214311959509587913208350055529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-453821943242679519262545820171294000000000000)
      constant := (8035776341546182398727907162312118614260892839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20606781822127305159/5000000000000000000)
  centralHi := (412135636442546103181/100000000000000000000)
  directionLo := (207577492749760194609/50000000000000000000)
  directionHi := (415154985499520389219/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree070.table
  base := (-231001405937463823710807127387255977139/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-597361258610622374493651309129694287000000000000)
      constant := (10712782557900455223472915909682271175826090558996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree070.table
  base := (-369607955292289025821520364198541099679/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (1277611931093112715193682578288000000000000)
      linear := (-92079212577622019850669652901234800000000000)
      constant := (1655146707562940331791515149550853677473505489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207577492749760194609/50000000000000000000)
  centralHi := (415154985499520389219/100000000000000000000)
  directionLo := (209076266673378923767/50000000000000000000)
  directionHi := (83630506669351569507/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree071.table
  base := (-1380335899562596200002121178957245189303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-1211782264671142121555227544292680454000000000000)
      constant := (22056187816855110971818501372835786972131166314273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree071.table
  base := (-345090093592710530544920196184226982949/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-233485091266770339622075354420527000000000000)
      constant := (4259644688391244052693035685352310071875788118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209076266673378923767/50000000000000000000)
  centralHi := (83630506669351569507/20000000000000000000)
  directionLo := (210564372760158480437/50000000000000000000)
  directionHi := (3369029964162535687/800000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree072.table
  base := (-446159407388728863728032940296730783479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (275940090)
      previous := (137970045)
      next := (137970045)
      square := (923074620214773936727435662813080000000000000)
      linear := (-68269000673391083006841803906998463000000000000)
      constant := (1260896102611301986743374023836309349121122602521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree072.table
  base := (-892339807389256362732429617514675322409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-473544302178971259234953153175934000000000000)
      constant := (8766443814597805130938107960701274809504562919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210564372760158480437/50000000000000000000)
  centralHi := (3369029964162535687/800000000000000000)
  directionLo := (212042035610112182653/50000000000000000000)
  directionHi := (424084071220224365307/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree073.table
  base := (-191981783962076959308340671448585010089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-622950879785468433345538698179632107000000000000)
      constant := (11672695553801688610180494054601155301944339043199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree073.table
  base := (-383981570302053791921552264329847007737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-480118421824401839225755597510814000000000000)
      constant := (9017196814184474788343964654591686653094918167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212042035610112182653/50000000000000000000)
  centralHi := (424084071220224365307/100000000000000000000)
  directionLo := (427018944101927146393/100000000000000000000)
  directionHi := (213509472050963573197/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree074.table
  base := (28945363466511285760868120118778701869/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (993384324)
      previous := (496692162)
      next := (496692162)
      square := (3323068632773186172218768386127088000000000000)
      linear := (-252592301404166847851800464478511218800000000000)
      constant := (4800794303043980556302476561884429428768381502821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree074.table
  base := (144711382149812037448665155473027728511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-486692541469832419216558041845694000000000000)
      constant := (9271548344195650301361940780935729351171773199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427018944101927146393/100000000000000000000)
  centralHi := (213509472050963573197/50000000000000000000)
  directionLo := (214966891509558530609/50000000000000000000)
  directionHi := (429933783019117061219/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree075.table
  base := (693749783538936432676803069236210043979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-142224583830081290202991916491760886000000000000)
      constant := (2741318999920290112469531548646314301731049657979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree075.table
  base := (693736551877868379462114709297120674189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-493266661115262999207360486180574000000000000)
      constant := (9529498378129111062630612350676483153232471101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214966891509558530609/50000000000000000000)
  centralHi := (429933783019117061219/100000000000000000000)
  directionLo := (216414496360764658777/50000000000000000000)
  directionHi := (86565798544305863511/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree076.table
  base := (315775791906489650582125211649362055121/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-648540500960314492197426087229569927000000000000)
      constant := (12674544750051877850151167623797137309786534740178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree076.table
  base := (1263091826928842010091946916801564428951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-499840780760693579198162930515454000000000000)
      constant := (9791046893579144796516278517677011797026741159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216414496360764658777/50000000000000000000)
  centralHi := (86565798544305863511/20000000000000000000)
  directionLo := (108926241127751824209/25000000000000000000)
  directionHi := (435704964511007296837/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree077.table
  base := (1852785140146516250930741633737612948497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-1314140749370526356962777100492431734000000000000)
      constant := (26035626967201556918801725621999303940839342754473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree077.table
  base := (463193855463618186257868309124246495647/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-253207450203062079594482687425167000000000000)
      constant := (5028096935801965455361814811600327262144638046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108926241127751824209/25000000000000000000)
  centralHi := (435704964511007296837/100000000000000000000)
  directionLo := (219281038429421991517/50000000000000000000)
  directionHi := (87712415371768796607/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree078.table
  base := (492558830774428736093552320956829833933/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (110376036)
      previous := (55188018)
      next := (55188018)
      square := (369229848085909574690974265125232000000000000)
      linear := (-29582233262676082878460045033904969200000000000)
      constant := (594032963508483965782149262041753665827668411933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree078.table
  base := (2462785827287692194227906656441413324861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-512989020051554739179767819185214000000000000)
      constant := (10324939296190594176702595649837718953963450349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219281038429421991517/50000000000000000000)
  centralHi := (87712415371768796607/20000000000000000000)
  directionLo := (220700347993578742629/50000000000000000000)
  directionHi := (441400695987157485259/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree079.table
  base := (3093128900307676966351833641031623917977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-1348260244270321102098626952559015494000000000000)
      constant := (27436658636037792994695759693830005898177272599793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree079.table
  base := (3093121767303898887671363846233519238977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-519563139696985319170570263520094000000000000)
      constant := (10597283153802850497457841745335977405606306993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220700347993578742629/50000000000000000000)
  centralHi := (441400695987157485259/100000000000000000000)
  directionLo := (3470477940756476227/781250000000000000)
  directionHi := (444221176416828957057/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree080.table
  base := (3743788272904313424530609349477477951517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-1365319991720218474666551878592307374000000000000)
      constant := (28151152771135482902095889669824928591891461661653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree080.table
  base := (467972770420683522513190057469166295803/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-263068629671207949580686353927487000000000000)
      constant := (5436612716499247106563921782353721540928696108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3470477940756476227/781250000000000000)
  centralHi := (444221176416828957057/100000000000000000000)
  directionLo := (223511930742161907203/50000000000000000000)
  directionHi := (447023861484323814407/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree081.table
  base := (4414771335939358714465296714178279810831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-153597748796679538581608533847288806000000000000)
      constant := (3208329526372723081473336692014067983578287656831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree081.table
  base := (882953220766634453042553894105829276733/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (1277611931093112715193682578288000000000000)
      linear := (-106542275797569295830435030437970800000000000)
      constant := (2230553224821188951183075523001655542796860397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223511930742161907203/50000000000000000000)
  centralHi := (447023861484323814407/100000000000000000000)
  directionLo := (44980908382952914001/10000000000000000000)
  directionHi := (449809083829529140011/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree082.table
  base := (5106077298189852581331654825120721174257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-1399439486620013219802401730658891134000000000000)
      constant := (29608097512861854001909918971645980259168938226313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree082.table
  base := (638259102273135099752311370130926019139/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-269642749316638529571488798262367000000000000)
      constant := (5717952609475367483395304076766789976548182604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44980908382952914001/10000000000000000000)
  centralHi := (449809083829529140011/100000000000000000000)
  directionLo := (45257716585656950521/10000000000000000000)
  directionHi := (452577165856569505211/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree083.table
  base := (290885274533084645729647496010448741841/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27594009000000000000000000000000000000000000000
      center := (496692162)
      previous := (248346081)
      next := (248346081)
      square := (1661534316386593086109384193063544000000000000)
      linear := (-141649923406991059237032665669218301400000000000)
      constant := (3035054807919729243346048627412115769802798461138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree083.table
  base := (5817701655216187494342991405233904807121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-545859618278707639133780040859614000000000000)
      constant := (11722642710624230934084672811665228496098746689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45257716585656950521/10000000000000000000)
  centralHi := (452577165856569505211/100000000000000000000)
  directionLo := (113832105042352087133/25000000000000000000)
  directionHi := (455328420169408348533/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree084.table
  base := (3274827673874801172275089855674751439663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (275940090)
      previous := (137970045)
      next := (137970045)
      square := (923074620214773936727435662813080000000000000)
      linear := (-79642165639989331385458421262526383000000000000)
      constant := (1727906523375194772984708974395748360588758197663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree084.table
  base := (6549652064604201563438011304926435734553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-552433737924138219124582485194494000000000000)
      constant := (12012978593288063474798523304387220556707872777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113832105042352087133/25000000000000000000)
  centralHi := (455328420169408348533/100000000000000000000)
  directionLo := (114515787495975233007/25000000000000000000)
  directionHi := (458063149983900932029/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree085.table
  base := (3650963195649745373009085574495689287239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 477405000000000000000000000000000000000000000
      center := (8593290)
      previous := (4296645)
      next := (4296645)
      square := (28746268449595036091857858011480000000000000)
      linear := (-2509720984376652833055668700274683000000000000)
      constant := (55126999177052432831144591652001821658834866959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree085.table
  base := (3650961790660908336106370455662940399989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-279503928784784399557692464764687000000000000)
      constant := (6153456431004378948022199615537273134703483301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114515787495975233007/25000000000000000000)
  centralHi := (458063149983900932029/100000000000000000000)
  directionLo := (230390824758918171571/50000000000000000000)
  directionHi := (460781649517836343143/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree086.table
  base := (8074518217126158393572011141364726106591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-1467678476419602710074101434792058654000000000000)
      constant := (32633812378792603182600751000643389203467807013319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree086.table
  base := (1614903162491199599115514795492003686139/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (1277611931093112715193682578288000000000000)
      linear := (-113116395442999875821237474772850800000000000)
      constant := (2520889102523579962272584991810615467106248651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230390824758918171571/50000000000000000000)
  centralHi := (460781649517836343143/100000000000000000000)
  directionLo := (463484204360388767857/100000000000000000000)
  directionHi := (231742102180194383929/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree087.table
  base := (8867430483608140269680377205344048371049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-164970913763277786960225151202816726000000000000)
      constant := (3712615330521743461337260905122356892149684605049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree087.table
  base := (8867428426062670702116915535088788004091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-572156096860429959096989818199134000000000000)
      constant := (12905576541593894530867612441304754951935401419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463484204360388767857/100000000000000000000)
  centralHi := (231742102180194383929/50000000000000000000)
  directionLo := (93234218364458243059/20000000000000000000)
  directionHi := (7283923309723300239/1562500000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree088.table
  base := (968066290203974283636966784331929259861/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27594009000000000000000000000000000000000000000
      center := (496692162)
      previous := (248346081)
      next := (248346081)
      square := (1661534316386593086109384193063544000000000000)
      linear := (-150179797131939745520995128685864241400000000000)
      constant := (3420258230407902257886728000974305612183967772749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree088.table
  base := (4840330570871281430901549176621850791349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-289365108252930269543896131267007000000000000)
      constant := (6605152972980993089326399078088117215045421541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93234218364458243059/20000000000000000000)
  centralHi := (7283923309723300239/1562500000000000000)
  directionLo := (23442129063397351571/5000000000000000000)
  directionHi := (468842581267947031421/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree089.table
  base := (1314276903558700470467764972942607036077/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-759428859384647413888938106445967147000000000000)
      constant := (17500472680105500687701543371384196751897888250772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree089.table
  base := (5257106861336234502441658269633413544067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-292652168075645559539297353434447000000000000)
      constant := (6759316861604858683944937292976153884289006803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23442129063397351571/5000000000000000000)
  centralHi := (468842581267947031421/100000000000000000000)
  directionLo := (7367170850478203333/1562500000000000000)
  directionHi := (471498934430605013313/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree090.table
  base := (11368087256796794431424437134228348096701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-170657496246576911149533459880580686000000000000)
      constant := (3978736348600497406931536670553308114492833362701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree090.table
  base := (284202149221680614737047994286972070539/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (190962)
      previous := (95481)
      next := (95481)
      square := (638805965546556357596841289144000000000000)
      linear := (-59187845579672169906939715120377400000000000)
      constant := (1383055987121544548795408295637027946785393004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7367170850478203333/1562500000000000000)
  centralHi := (471498934430605013313/100000000000000000000)
  directionLo := (118535101427910483403/25000000000000000000)
  directionHi := (474140405711641933613/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree091.table
  base := (12242278812930753437070958105899633066529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-1552977213669089572913726064958518054000000000000)
      constant := (36625627630855591921658131073847268564434498824761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree091.table
  base := (3060569427870593144443804967957285230593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-299226287721076139530099797769327000000000000)
      constant := (7073042194093949847065575879774604678022722274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118535101427910483403/25000000000000000000)
  centralHi := (474140405711641933613/100000000000000000000)
  directionLo := (476767242464921098311/100000000000000000000)
  directionHi := (59595905308115137289/12500000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree092.table
  base := (6568394874925587889457724146572034799007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-785018480559493472740825495495904967000000000000)
      constant := (18725973418253733766912253685645934606392112349063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree092.table
  base := (13136788807996838831910672728359226612381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-605026695087582859051002039873534000000000000)
      constant := (14465207272615073910892603355005331035130750029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476767242464921098311/100000000000000000000)
  centralHi := (59595905308115137289/12500000000000000000)
  directionLo := (239689842633563277601/50000000000000000000)
  directionHi := (479379685267126555203/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree093.table
  base := (7025809971714611719404570183809085784823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (275940090)
      previous := (137970045)
      next := (137970045)
      square := (923074620214773936727435662813080000000000000)
      linear := (-88172039364938017669420884279172323000000000000)
      constant := (2127088041718605068080589982128686603575353102823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree093.table
  base := (14051619138139739854352972153147835953789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-611600814733013439041804484208414000000000000)
      constant := (14787928523221014335213085679390987391633747501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239689842633563277601/50000000000000000000)
  centralHi := (479379685267126555203/100000000000000000000)
  directionLo := (481977968174909175381/100000000000000000000)
  directionHi := (240988984087454587691/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree094.table
  base := (3746692322223194134908164465731720434701/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-802078228009390845308750421529196847000000000000)
      constant := (19566270685623390088849078513316322056021246612618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree094.table
  base := (14986768600446423622232218433207748739597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-618174934378444019032606928543294000000000000)
      constant := (15114248138929282473781971966651097006378384573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481977968174909175381/100000000000000000000)
  centralHi := (240988984087454587691/50000000000000000000)
  directionLo := (242281159484811267357/50000000000000000000)
  directionHi := (96912463793924506943/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree095.table
  base := (15942237697836508842246661300482862879739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-1621216203468679063185425769091685574000000000000)
      constant := (39986816695003677022676372330414530665149283883651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree095.table
  base := (15942237109346583088114798150538568277457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-624749054023874599023409372878174000000000000)
      constant := (15444166118832062939133039012034093670855541313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242281159484811267357/50000000000000000000)
  centralHi := (96912463793924506943/20000000000000000000)
  directionLo := (243566479695186433101/50000000000000000000)
  directionHi := (487132959390372866203/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree096.table
  base := (4229506273923213405205433112533583153743/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (275940090)
      previous := (137970045)
      next := (137970045)
      square := (923074620214773936727435662813080000000000000)
      linear := (-91015330606587579764075038618054303000000000000)
      constant := (2269467262230442425169146005030802564965918383486) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree096.table
  base := (1691802459270228226446325904304905741463/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (190962)
      previous := (95481)
      next := (95481)
      square := (638805965546556357596841289144000000000000)
      linear := (-63132317366930517901421181721305400000000000)
      constant := (1577768246216404436837450198449145145011180967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243566479695186433101/50000000000000000000)
  centralHi := (487132959390372866203/100000000000000000000)
  directionLo := (244845052678028961771/50000000000000000000)
  directionHi := (489690105356057923543/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree097.table
  base := (895706570979642721775889607971223803401/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27594009000000000000000000000000000000000000000
      center := (496692162)
      previous := (248346081)
      next := (248346081)
      square := (1661534316386593086109384193063544000000000000)
      linear := (-165533569836847380832127562115826933400000000000)
      constant := (4172332344494483351898136920435878490294122849218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree097.table
  base := (8957065494863209712845965178699884156187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-318948646657367879502507130773967000000000000)
      constant := (8057398584140168199649811251500496071012987883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244845052678028961771/50000000000000000000)
  centralHi := (489690105356057923543/100000000000000000000)
  directionLo := (492233967177024017807/100000000000000000000)
  directionHi := (30764622948564001113/6250000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree098.table
  base := (18930556616556832532932534371864883083257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-1672395445818371180889200547191561214000000000000)
      constant := (42605554867932364888148103657884051167583341407313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree098.table
  base := (18930556249222878339164667216122416660779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-644471412960166338995816705882814000000000000)
      constant := (16455510236637799434796363706557654718354204411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492233967177024017807/100000000000000000000)
  centralHi := (30764622948564001113/6250000000000000000)
  directionLo := (494764749756928426191/100000000000000000000)
  directionHi := (30922796859808026637/6250000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree099.table
  base := (9983650320982027618993720008791431685151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (275940090)
      previous := (137970045)
      next := (137970045)
      square := (923074620214773936727435662813080000000000000)
      linear := (-93858621848237141858729192956936283000000000000)
      constant := (2416505832659960714529006706678305906588104651151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree099.table
  base := (19967300328098688877312076701391290006329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-651045532605596918986619150217694000000000000)
      constant := (16799821666779260154781341905696226195677144361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494764749756928426191/100000000000000000000)
  centralHi := (30922796859808026637/6250000000000000000)
  directionLo := (497282652785355520103/100000000000000000000)
  directionHi := (62160331598169440013/12500000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree100.table
  base := (525609086456460430283825909674700477461/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27594009000000000000000000000000000000000000000
      center := (496692162)
      previous := (248346081)
      next := (248346081)
      square := (1661534316386593086109384193063544000000000000)
      linear := (-170651494071816592602505039925814497400000000000)
      constant := (4439797380374929393036501486742145853189452524596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree100.table
  base := (21024363190106188502639917407091115727389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-657619652251027498977421594552574000000000000)
      constant := (17147731458320167107394280693339229646751869901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497282652785355520103/100000000000000000000)
  centralHi := (62160331598169440013/12500000000000000000)
  directionLo := (62473483865212380557/12500000000000000000)
  directionHi := (499787870921699044457/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree101.table
  base := (4420349006770753665860600807498915765259/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (993384324)
      previous := (496692162)
      next := (496692162)
      square := (3323068632773186172218768386127088000000000000)
      linear := (-344714937633612659718595065058287370800000000000)
      constant := (9061632262934155916777466185456864209416798733331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree101.table
  base := (5525436201194915531997829964163414019147/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-332096885948229039484112019443727000000000000)
      constant := (8749619805468654760637766420604876318658261046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62473483865212380557/12500000000000000000)
  centralHi := (499787870921699044457/100000000000000000000)
  directionLo := (251140296985394875877/50000000000000000000)
  directionHi := (100456118794157950351/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree102.table
  base := (289993066777601548592977523548446126371/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (190962)
      previous := (95481)
      next := (95481)
      square := (638805965546556357596841289144000000000000)
      linear := (-66921739162551352216874288786033400000000000)
      constant := (1777303633983519802279047161134182019637359512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree102.table
  base := (11599722573268211268544988765083191593453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-335383945770944329479513241611167000000000000)
      constant := (8927173062179640333873811506719021579614942877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251140296985394875877/50000000000000000000)
  centralHi := (100456118794157950351/20000000000000000000)
  directionLo := (20190440282028673121/4000000000000000000)
  directionHi := (252380503525358414013/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree103.table
  base := (24317464361040731926265278914750851799189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (468180)
      previous := (234090)
      next := (234090)
      square := (1566155449511351763700051082160000000000000)
      linear := (-165679534646795932107533714521446000000000000)
      constant := (4444951684311074566918658205827177465529690589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree103.table
  base := (24317464193916931486609708675895053983843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (180)
      previous := (90)
      next := (90)
      square := (602135889854422054479066160000000000000)
      linear := (-63845980882959679418402198846000000000000)
      constant := (1716754736389708389630229404073895053983843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20190440282028673121/4000000000000000000)
  centralHi := (252380503525358414013/50000000000000000000)
  directionLo := (126807322688315759491/25000000000000000000)
  directionHi := (101445858150652607593/20000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree104.table
  base := (6363950517917495405223846511060646227707/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-887376965258877708148375051695656247000000000000)
      constant := (24047318005494899558068467667585165161106326014726) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree104.table
  base := (2545580192894248351898073978218725815877/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (190962)
      previous := (95481)
      next := (95481)
      square := (638805965546556357596841289144000000000000)
      linear := (-68391613083274981894063137189209400000000000)
      constant := (1857535423274398034859461731717036062180639093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126807322688315759491/25000000000000000000)
  centralHi := (101445858150652607593/20000000000000000000)
  directionLo := (254842810648673539091/50000000000000000000)
  directionHi := (509685621297347078183/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree105.table
  base := (26614458458453528296719620476177380999527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-199090408663072532096075003269400486000000000000)
      constant := (5449122032875615796070714201612416793821930781527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree105.table
  base := (26614458336572290933581860632151131642711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-690490250478180398931433816226974000000000000)
      constant := (18941255827356405080054273302298261355597520999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254842810648673539091/50000000000000000000)
  centralHi := (509685621297347078183/100000000000000000000)
  directionLo := (256065085337921045579/50000000000000000000)
  directionHi := (512130170675842091159/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree106.table
  base := (13896716754157439919814314448205809883779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-904436712708775080716299977728948127000000000000)
      constant := (24999439636583793192426679910655064656285286680011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree106.table
  base := (13896716702122306383644561949993498640431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-348532185061805489461118130280927000000000000)
      constant := (9655377891031211495044144873012123027076332479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256065085337921045579/50000000000000000000)
  centralHi := (512130170675842091159/100000000000000000000)
  directionLo := (257281553398058252427/50000000000000000000)
  directionHi := (102912621359223300971/20000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree107.table
  base := (5798545442068623305222315180973597083801/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (993384324)
      previous := (496692162)
      next := (496692162)
      square := (3323068632773186172218768386127088000000000000)
      linear := (-365186634573489506800104976298237626800000000000)
      constant := (10192995788509971151947779170387642554792778548209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree107.table
  base := (28992727121488942067903878619142737128087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-703638489769041558913038704896734000000000000)
      constant := (19683854096750952470440791160244163298191874983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257281553398058252427/50000000000000000000)
  centralHi := (102912621359223300971/20000000000000000000)
  directionLo := (516984593614622183973/100000000000000000000)
  directionHi := (258492296807311091987/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree108.table
  base := (30212339555454469675613413471756068444387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-204776991146371656285383311947164446000000000000)
      constant := (5771155255975188077174209087340725855606558986387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree108.table
  base := (7553084869899567761914432352719277219483/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-355106304707236069451920574615807000000000000)
      constant := (10030275385664810437745671319192473624042990294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516984593614622183973/100000000000000000000)
  centralHi := (258492296807311091987/50000000000000000000)
  directionLo := (103878958253167036213/20000000000000000000)
  directionHi := (259697395632917590533/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree109.table
  base := (31452270536106221611021985723548124441843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-1860052667767242279136374733557771894000000000000)
      constant := (52925134356639963369873625700511561651281335718587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree109.table
  base := (1258090818854085976078050672724682425379/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (1277611931093112715193682578288000000000000)
      linear := (-143357345811980543778928718713298800000000000)
      constant := (4088169161144365289591689809103301979254229055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103878958253167036213/20000000000000000000)
  centralHi := (259697395632917590533/50000000000000000000)
  directionLo := (130448464046459010699/25000000000000000000)
  directionHi := (521793856185836042797/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree110.table
  base := (32712520146054858919934997301405076869299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-1877112415217139651704299659591063774000000000000)
      constant := (53919190100967384220362677945520835918777128429691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree110.table
  base := (4089065011347835621011444209234612857049/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-361680424352666649442723018950687000000000000)
      constant := (10412369599932127909944050505617150031201731364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130448464046459010699/25000000000000000000)
  centralHi := (521793856185836042797/100000000000000000000)
  directionLo := (524181941230799552423/100000000000000000000)
  directionHi := (65522742653849944053/12500000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree111.table
  base := (424913604751895676911785571922834728709/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3066001000000000000000000000000000000000000000
      center := (55188018)
      previous := (27594009)
      next := (27594009)
      square := (184614924042954787345487132562616000000000000)
      linear := (-21046357362967078047469162062492840600000000000)
      constant := (610250717073520902382860921181791537458452181672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree111.table
  base := (33993088332976848398646115021529171295181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-729934968350763878876248482236254000000000000)
      constant := (21212230953704786662933387408723456978270575229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524181941230799552423/100000000000000000000)
  centralHi := (65522742653849944053/12500000000000000000)
  directionLo := (526559195790647876943/100000000000000000000)
  directionHi := (32909949736915492309/6250000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree112.table
  base := (17646987617084951370698124687937326148513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-955615955058467198420074755828823767000000000000)
      constant := (27967628831735911314125195592911579293178003058617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree112.table
  base := (1411759007756378752521650332574352553823/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (1277611931093112715193682578288000000000000)
      linear := (-147301817599238891773410185314226800000000000)
      constant := (4320664213440143187844460386751176131217541035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526559195790647876943/100000000000000000000)
  centralHi := (32909949736915492309/6250000000000000000)
  directionLo := (52892576589810624757/10000000000000000000)
  directionHi := (528925765898106247571/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree113.table
  base := (36615180704658931561813708217728090921779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-1928291657566831769408074437690939414000000000000)
      constant := (56957269481436990556515996162957747159948388022011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree113.table
  base := (9153795167575543592918170707289735637241/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-371541603820812519428926685453007000000000000)
      constant := (10999004770158631700954241279979534610750979538) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52892576589810624757/10000000000000000000)
  centralHi := (528925765898106247571/100000000000000000000)
  directionLo := (132820448583346613521/25000000000000000000)
  directionHi := (106256358866677290817/20000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree114.table
  base := (7591340957764149634014278009354184656087/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (110376036)
      previous := (55188018)
      next := (55188018)
      square := (369229848085909574690974265125232000000000000)
      linear := (-43230031222593980932799985860538473200000000000)
      constant := (1288635555343003937123760284756082297309747398087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree114.table
  base := (18978352379752132414821843109503866223649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-374828663643527809424327907620447000000000000)
      constant := (11198148186513153886046910086067264516766692241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132820448583346613521/25000000000000000000)
  centralHi := (106256358866677290817/20000000000000000000)
  directionLo := (533627420724710502583/100000000000000000000)
  directionHi := (66703427590588812823/12500000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree115.table
  base := (39318547484405836385391734262267600248881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-1962411152466626514543924289757523174000000000000)
      constant := (59029249190404309300672019504806285094176024553929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree115.table
  base := (39318547459392123039785021037884761195609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-756231446932486198839458259575774000000000000)
      constant := (22798181565305319595463996224127429431524215881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533627420724710502583/100000000000000000000)
  centralHi := (66703427590588812823/12500000000000000000)
  directionLo := (535962781644874704129/100000000000000000000)
  directionHi := (53596278164487470413/10000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree116.table
  base := (10175177197406285620039288181025779670931/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-989735449958261943555924607895407527000000000000)
      constant := (30039608540647509891081526479804432823943374104758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree116.table
  base := (40700708768284296563700704576294001793107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-762805566577916778830260703910654000000000000)
      constant := (23203665117136460343100067735372727065023072163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535962781644874704129/100000000000000000000)
  centralHi := (53596278164487470413/10000000000000000000)
  directionLo := (134572002676010791513/25000000000000000000)
  directionHi := (538288010704043166053/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree117.table
  base := (5262898587884468979300214439044284021941/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (275940090)
      previous := (137970045)
      next := (137970045)
      square := (923074620214773936727435662813080000000000000)
      linear := (-110918369298134514426654118990228163000000000000)
      constant := (3396583536837144254244041207140428600172220511764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree117.table
  base := (4210318868486982379401500988565946860249/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (190962)
      previous := (95481)
      next := (95481)
      square := (638805965546556357596841289144000000000000)
      linear := (-76937968622334735882106314824553400000000000)
      constant := (2361274702850582202330938561867297930240381641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134572002676010791513/25000000000000000000)
  centralHi := (538288010704043166053/100000000000000000000)
  directionLo := (540603238638949090753/100000000000000000000)
  directionHi := (270301619319474545377/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree118.table
  base := (43525987223678141324223936896714654368849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-2013590394816318632247699067857398814000000000000)
      constant := (62207108935695251312564440099207386010085908625641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree118.table
  base := (21762993604073876894000400569765332041301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-387976902934388969405932796290207000000000000)
      constant := (12012713649701392773770278845022686407626162309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540603238638949090753/100000000000000000000)
  centralHi := (270301619319474545377/50000000000000000000)
  directionLo := (271454296699336197953/50000000000000000000)
  directionHi := (542908593398672395907/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree119.table
  base := (44969104350623218743523439293571479209637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (17186580)
      previous := (8593290)
      next := (8593290)
      square := (57492536899190072183715716022960000000000000)
      linear := (-7026471080505937732926034580936646000000000000)
      constant := (218979352592223729733775724559523424906415350397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree119.table
  base := (22484552168688062965121444762156087289927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-391263962757104259401334018457647000000000000)
      constant := (12220852964909739727812322105683236930058835543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271454296699336197953/50000000000000000000)
  centralHi := (542908593398672395907/100000000000000000000)
  directionLo := (136301050056788226599/25000000000000000000)
  directionHi := (545204200227152906397/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree120.table
  base := (46432540083327636355250396114155329025039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-227523321079568153042616546658220286000000000000)
      constant := (7152475061491635490575188008408158172946098599039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree120.table
  base := (23216270036014471758165956046706533543227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-394551022579819549396735240625087000000000000)
      constant := (12430791459875161724262283125567949614360095243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136301050056788226599/25000000000000000000)
  centralHi := (545204200227152906397/100000000000000000000)
  directionLo := (6843627271782371093/1250000000000000000)
  directionHi := (547490181742589687441/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree121.table
  base := (4791629442139609896977369145558097092083/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27594009000000000000000000000000000000000000000
      center := (496692162)
      previous := (248346081)
      next := (248346081)
      square := (1661534316386593086109384193063544000000000000)
      linear := (-206476963716601074995147384595727445400000000000)
      constant := (6546883689850052809989062541421658904331812130747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree121.table
  base := (47916294411759901937563930340737563953259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-795676164805069678784272925585054000000000000)
      constant := (25285058269191643580646583725742478815980124731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6843627271782371093/1250000000000000000)
  centralHi := (547490181742589687441/100000000000000000000)
  directionLo := (549766658013868948901/100000000000000000000)
  directionHi := (274883329006934474451/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree122.table
  base := (24710183682294792150082546089250118242709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-1040914692307954061259699385995283167000000000000)
      constant := (33287358467186744182033143082865247322540376330381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree122.table
  base := (12355091839092955934590332810019148624217/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-401125142225250129387537684959967000000000000)
      constant := (12856065989070673998182236869295580295508636306) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549766658013868948901/100000000000000000000)
  centralHi := (274883329006934474451/50000000000000000000)
  directionLo := (552033746634155314869/100000000000000000000)
  directionHi := (55203374663415531487/10000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree123.table
  base := (50944758912798560285015761915652236035103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-233209903562867277231924855335984246000000000000)
      constant := (7521101740115619753223930038535268451835861833103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree123.table
  base := (50944758905790914817211964803620628551593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-808824404095930838765877814254814000000000000)
      constant := (26142804046598653814055293890461273248303850137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (552033746634155314869/100000000000000000000)
  centralHi := (55203374663415531487/10000000000000000000)
  directionLo := (277145781395887042591/50000000000000000000)
  directionHi := (554291562791774085183/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree124.table
  base := (52489469066020425283709505186561913425067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-2115948879515702867655248624057150094000000000000)
      constant := (68814433078501724555043299893843365284108519623603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree124.table
  base := (13122367265011273254421089656124348149993/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-407699261870680709378340129294847000000000000)
      constant := (13288537237281928607060731345294154419046551474) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277145781395887042591/50000000000000000000)
  centralHi := (554291562791774085183/100000000000000000000)
  directionLo := (556540219338505384297/100000000000000000000)
  directionHi := (278270109669252692149/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree125.table
  base := (54054497824340516500122862587910347956943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-2133008626965600240223173550090441974000000000000)
      constant := (69948269186759283487721878902922025370217016754487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree125.table
  base := (1351362445481143904310089546939052650699/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (190962)
      previous := (95481)
      next := (95481)
      square := (638805965546556357596841289144000000000000)
      linear := (-82197264338679199874748270292457400000000000)
      constant := (2701494326203814001616929949784830638285062764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556540219338505384297/100000000000000000000)
  centralHi := (278270109669252692149/50000000000000000000)
  directionLo := (69847478356925596001/12500000000000000000)
  directionHi := (558779826855404768009/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree126.table
  base := (1112796903758322660625718034223956604523/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3066001000000000000000000000000000000000000000
      center := (55188018)
      previous := (27594009)
      next := (27594009)
      square := (184614924042954787345487132562616000000000000)
      linear := (-23889648604616640142123316401374820600000000000)
      constant := (789904710953528834330558299249376262967120612615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree126.table
  base := (27819922591786227293553084144702345122909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-414273381516111289369142573629727000000000000)
      constant := (13728205204511703534696181599273329179408941581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69847478356925596001/12500000000000000000)
  centralHi := (558779826855404768009/100000000000000000000)
  directionLo := (561010493716258912403/100000000000000000000)
  directionHi := (140252623429064728101/25000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree127.table
  base := (57245511156963105403957765883266060451441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-2167128121865394985359023402157025734000000000000)
      constant := (72243897475682614990626270524202039991991607016969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree127.table
  base := (57245511153260015746924871432735199653657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-835120882677653158729087591594334000000000000)
      constant := (27901475915522149658580427175336245733125647113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (561010493716258912403/100000000000000000000)
  centralHi := (140252623429064728101/25000000000000000000)
  directionLo := (563232326148779416533/100000000000000000000)
  directionHi := (281616163074389708267/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree128.table
  base := (58871495731744515753788704873918583154789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-2184187869315292357926948328190317614000000000000)
      constant := (73405689656361602681168821891196761280840496059101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree128.table
  base := (58871495728587739029203936405878225441559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-841695002323083738719890035929214000000000000)
      constant := (28350139781537330870827736524465194093709499431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563232326148779416533/100000000000000000000)
  centralHi := (281616163074389708267/50000000000000000000)
  directionLo := (22617817131745299483/4000000000000000000)
  directionHi := (141361357073408121769/25000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree129.table
  base := (60517798912561233948591746061397107187219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-244583068529465525610541472691512166000000000000)
      constant := (8286311169762540040802018057913386183533120641219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree129.table
  base := (14774853249480062839847333305296481689/2441406250000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-424134560984257159355346240132047000000000000)
      constant := (14401201003536144747953234908130996486440654848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell088.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22617817131745299483/4000000000000000000)
  centralHi := (141361357073408121769/25000000000000000000)
  directionLo := (17739059445668666183/3125000000000000000)
  directionHi := (567649902261397317857/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree130.table
  base := (3109221034987199333819655372962335697653/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27594009000000000000000000000000000000000000000
      center := (496692162)
      previous := (248346081)
      next := (248346081)
      square := (1661534316386593086109384193063544000000000000)
      linear := (-221830736421508710306279818025690137400000000000)
      constant := (7575723009019551412398022806637490820304116321754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree130.table
  base := (62184420697450353045702800335922081945589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-854843241613944898701494924598974000000000000)
      constant := (29258262592130659564126184650617417367360753701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 130 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17739059445668666183/3125000000000000000)
  centralHi := (567649902261397317857/100000000000000000000)
  directionLo := (284922924093770654627/50000000000000000000)
  directionHi := (113969169637508261851/20000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree131.table
  base := (15967840273411680065753998601773492013669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-1117683555832492237815361553145096627000000000000)
      constant := (38473489171684665374777650493605281207423221018042) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree131.table
  base := (63871361091691816418889242381377343713017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-861417361259375478692297368933854000000000000)
      constant := (29717721536716303074304120544167166239451397353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 131 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284922924093770654627/50000000000000000000)
  centralHi := (113969169637508261851/20000000000000000000)
  directionLo := (8938021316960873023/1562500000000000000)
  directionHi := (572033364285495873473/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree132.table
  base := (65578620094641054981850140026760790871073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-250269651012764649799849781369276126000000000000)
      constant := (8682893920821618304123542226666510053571500689073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree132.table
  base := (32789310046487476747443140429089084717193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-433995740452403029341549906634367000000000000)
      constant := (15090389420416626921948618724471970099764700537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 132 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8938021316960873023/1562500000000000000)
  centralHi := (572033364285495873473/100000000000000000000)
  directionLo := (574212546897912424007/100000000000000000000)
  directionHi := (71776568362239053001/12500000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree133.table
  base := (13461239540622331981947356530418679121229/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (993384324)
      previous := (496692162)
      next := (496692162)
      square := (3323068632773186172218768386127088000000000000)
      linear := (-453897321312955844153314591671355402800000000000)
      constant := (15870886184456366129723668809378857963339305117061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree133.table
  base := (2692247908067671073182404617538921988723/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (1277611931093112715193682578288000000000000)
      linear := (-174913120110047327734780451520722800000000000)
      constant := (6129486900897134146822143975453912516891811535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 133 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (574212546897912424007/100000000000000000000)
  centralHi := (71776568362239053001/12500000000000000000)
  directionLo := (288191745273087117619/50000000000000000000)
  directionHi := (576383490546174235239/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree134.table
  base := (69054093919452403846976663125797616162347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-2286546354014676593334497884390068894000000000000)
      constant := (80572135248041996903295010853417952783562348579123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree134.table
  base := (69054093918242421121383985381751189682231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-881139720195667218664704701938494000000000000)
      constant := (31117688527677798773960670424447954371338788679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 134 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288191745273087117619/50000000000000000000)
  centralHi := (576383490546174235239/100000000000000000000)
  directionLo := (578546287978236165833/100000000000000000000)
  directionHi := (289273143989118082917/50000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree135.table
  base := (70822308744063160200289437850080498264489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-255956233496063773989158090047040086000000000000)
      constant := (9088795362742899734613973702089887580259421538489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree135.table
  base := (14164461748606421162202019602784601922491/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (1277611931093112715193682578288000000000000)
      linear := (-177542767968219559731101429254674800000000000)
      constant := (6318308182082787387298593671599939841795707019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 135 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (578546287978236165833/100000000000000000000)
  centralHi := (289273143989118082917/50000000000000000000)
  directionLo := (580701030214860753791/100000000000000000000)
  directionHi := (4536726798553599639/781250000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree136.table
  base := (3630542108867358132722417526771313317341/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 95481000000000000000000000000000000000000000
      center := (1718658)
      previous := (859329)
      next := (859329)
      square := (5749253689919007218371571602296000000000000)
      linear := (-802998563638225376633338317113028600000000000)
      constant := (28732006910804588099390082177499547133706072042) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree136.table
  base := (72610842176468625451847759871740389728363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-894287959486528378646309590608254000000000000)
      constant := (32068991652698411514124733010973197794628203067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 136 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580701030214860753791/100000000000000000000)
  centralHi := (4536726798553599639/781250000000000000)
  directionLo := (582847806594315898319/100000000000000000000)
  directionHi := (7285597582428948729/1250000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree137.table
  base := (14883938843941764892731913393948659131137/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (993384324)
      previous := (496692162)
      next := (496692162)
      square := (3323068632773186172218768386127088000000000000)
      linear := (-467545119272873742207654532497988906800000000000)
      constant := (16856232074134128454681203520503819512702526558233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree137.table
  base := (74419694218960284031267266288686160744567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-900862079131958958637112034943134000000000000)
      constant := (32550040754535554203857975846561369479339111303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 137 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (582847806594315898319/100000000000000000000)
  centralHi := (7285597582428948729/1250000000000000000)
  directionLo := (584986704815596232383/100000000000000000000)
  directionHi := (9140417262743691131/1562500000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree138.table
  base := (76248864871551947727904979288559219226583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-261642815979362898178466398724804046000000000000)
      constant := (9504015495559265347645880319874442887707922704583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree138.table
  base := (15249772974182840494161385663466322592353/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (1277611931093112715193682578288000000000000)
      linear := (-181487239755477907725582895855602800000000000)
      constant := (6606937643185936830309859361344188616382272977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 138 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (584986704815596232383/100000000000000000000)
  centralHi := (9140417262743691131/1562500000000000000)
  directionLo := (587117810980227348503/100000000000000000000)
  directionHi := (73389726372528418563/12500000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree139.table
  base := (15619670826655652092677477833660454813359/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (993384324)
      previous := (496692162)
      next := (496692162)
      square := (3323068632773186172218768386127088000000000000)
      linear := (-474369018252832691234824502911305658800000000000)
      constant := (17360087448064916491990541115462186470763921566231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree139.table
  base := (15619670826546987912472795909373490751131/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (1277611931093112715193682578288000000000000)
      linear := (-182802063684564023723743384722578800000000000)
      constant := (6704586807377018664284386728519928563378748779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 139 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (587117810980227348503/100000000000000000000)
  centralHi := (73389726372528418563/12500000000000000000)
  directionLo := (147310302408177314641/25000000000000000000)
  directionHi := (117848241926541851713/20000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree140.table
  base := (79968162005286228952176108779527615307929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-2388904838714060828742047440589820174000000000000)
      constant := (88074053711555220548998982836500045142555530597361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree140.table
  base := (79968162004823375917997614464887057259257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-920584438068250698609519367947774000000000000)
      constant := (34014778217406034655889222348516346790463457513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 140 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147310302408177314641/25000000000000000000)
  centralHi := (117848241926541851713/20000000000000000000)
  directionLo := (147839245949913209137/25000000000000000000)
  directionHi := (591356983799652836549/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree141.table
  base := (20464572121992525259190223589996724457501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (275940090)
      previous := (137970045)
      next := (137970045)
      square := (923074620214773936727435662813080000000000000)
      linear := (-133664699231331011183887353701284003000000000000)
      constant := (4964277159652010070803647087359424981116845047002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree141.table
  base := (16371657697515163677529073540260747586959/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (1277611931093112715193682578288000000000000)
      linear := (-185431711542736255720064362456530800000000000)
      constant := (6902044151499342514864430045871961071150048031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 141 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147839245949913209137/25000000000000000000)
  centralHi := (591356983799652836549/100000000000000000000)
  directionLo := (74183151878457562739/12500000000000000000)
  directionHi := (593465215027660501913/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree142.table
  base := (20942183395429785735271953458941370062483/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-1211512166806927786938948646328201967000000000000)
      constant := (45324621363439103026019831799543378313452972928694) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree142.table
  base := (20942183395345822263740487751442943793187/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-466866338679555929295562128308767000000000000)
      constant := (17504630828580637715003105061041050381403841766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 142 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74183151878457562739/12500000000000000000)
  centralHi := (593465215027660501913/100000000000000000000)
  directionLo := (148891495855000010617/25000000000000000000)
  directionHi := (595565983420000042469/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree143.table
  base := (1071243716086462975573012912042020487449/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27594009000000000000000000000000000000000000000
      center := (496692162)
      previous := (248346081)
      next := (248346081)
      square := (1661534316386593086109384193063544000000000000)
      linear := (-244008408106375294644582221868969581400000000000)
      constant := (9195081527099188224438078021239367129120816744328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree143.table
  base := (17139899457326193709073015882467500612033/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (1277611931093112715193682578288000000000000)
      linear := (-188061359400908487716385340190482800000000000)
      constant := (7102380183280761920839291713095886113993058097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 143 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148891495855000010617/25000000000000000000)
  centralHi := (595565983420000042469/100000000000000000000)
  directionLo := (597659367672118241127/100000000000000000000)
  directionHi := (74707420959014780141/12500000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree144.table
  base := (87650579603941420987257263067219229925699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-273015980945961146557083016080331966000000000000)
      constant := (10362411834009736700560002772311944370171423059699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree144.table
  base := (10956322450462221016474437957448328683299/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-473440458324986509286364572643647000000000000)
      constant := (18009069267614167483293761992068725276004476364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 144 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (597659367672118241127/100000000000000000000)
  centralHi := (74707420959014780141/12500000000000000000)
  directionLo := (599745445106038853347/100000000000000000000)
  directionHi := (149936361276509713337/25000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree145.table
  base := (89621980533163524625192019886258043298999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-2474203575963547691581672070756279574000000000000)
      constant := (94581916432175694036893346654327635090614968096991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree145.table
  base := (89621980532956009137596699898774524508073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-953455036295403598563531589622174000000000000)
      constant := (36527974513638801474098757316544828930506146457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 145 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599745445106038853347/100000000000000000000)
  centralHi := (149936361276509713337/25000000000000000000)
  directionLo := (300912145851843737371/50000000000000000000)
  directionHi := (601824291703687474743/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree146.table
  base := (45806850037473960477781842973805304148983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-1245631661706722532074798498394785727000000000000)
      constant := (47955722524633066721438632566836608161434774242847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree146.table
  base := (91613700074771191526377006674560395855901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-960029155940834178554334033957054000000000000)
      constant := (37041408851639086715844079426321855239635253709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 146 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300912145851843737371/50000000000000000000)
  centralHi := (601824291703687474743/100000000000000000000)
  directionLo := (120779196427836786911/20000000000000000000)
  directionHi := (150973995534795983639/25000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree147.table
  base := (5851608639353271251534333079822782889927/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (275940090)
      previous := (137970045)
      next := (137970045)
      square := (923074620214773936727435662813080000000000000)
      linear := (-139351281714630135373195662379047963000000000000)
      constant := (5402794019853823318283642267752455429556392575416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree147.table
  base := (18725147645900367286438251607198670970653/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (1277611931093112715193682578288000000000000)
      linear := (-193320655117252951709027295658386800000000000)
      constant := (7511688309846598848506935609578978300327657677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 147 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120779196427836786911/20000000000000000000)
  centralHi := (150973995534795983639/25000000000000000000)
  directionLo := (18936268431566907643/3125000000000000000)
  directionHi := (605960589810141044577/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree148.table
  base := (47829047498813776710733737311362865272823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-1262691409156619904642723424428077607000000000000)
      constant := (49299229178246716044985416693849129487604065317407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree148.table
  base := (95658094997499389801423951469249865540743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-973177395231695338535938922626814000000000000)
      constant := (38079072606424252544215746315094783823521742487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 148 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18936268431566907643/3125000000000000000)
  centralHi := (605960589810141044577/100000000000000000000)
  directionLo := (608018186868006818997/100000000000000000000)
  directionHi := (304009093434003409499/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree149.table
  base := (97710770379217311055607281856478693573161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-2542442565763137181853371774889447094000000000000)
      constant := (99955943046649455963563757099250897232266046792449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree149.table
  base := (6106923148694261022457711231394717128941/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-489875757438562959263370683480847000000000000)
      constant := (19301651011608257280948721682736365432167480552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 149 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (608018186868006818997/100000000000000000000)
  centralHi := (304009093434003409499/50000000000000000000)
  directionLo := (305034422123742826633/50000000000000000000)
  directionHi := (610068844247485653267/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree150.table
  base := (19956752874951664343956918137172383787701/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (110376036)
      previous := (55188018)
      next := (55188018)
      square := (369229848085909574690974265125232000000000000)
      linear := (-56877829182511878987139926687171977200000000000)
      constant := (2251616587285470722118748252676260620865475053701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree150.table
  base := (4989188218733269741876083967519467178397/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (190962)
      previous := (95481)
      next := (95481)
      square := (638805965546556357596841289144000000000000)
      linear := (-98632563452255649851754381129657400000000000)
      constant := (3913112979961335763692365453637938054591227546) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 150 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (305034422123742826633/50000000000000000000)
  centralHi := (610068844247485653267/100000000000000000000)
  directionLo := (153028157923768101107/25000000000000000000)
  directionHi := (612112631695072404429/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree151.table
  base := (101877076984580269461238064793069678295553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-2576562060662931926989221626956030854000000000000)
      constant := (102698868500092708989877236312035192967014594141977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree151.table
  base := (101877076984501146853364850866137794273543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-992899754167987078508346255631454000000000000)
      constant := (39662555935618283817352803546617069859448017687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 151 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153028157923768101107/25000000000000000000)
  centralHi := (612112631695072404429/100000000000000000000)
  directionLo := (614149617796731846957/100000000000000000000)
  directionHi := (307074808898365923479/50000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree152.table
  base := (25997677052251464765463944918244386404683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-1296810904056414649778573276494661367000000000000)
      constant := (52042154631698970082910107258129784179300600688294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree152.table
  base := (103990708208938493059136609566216053870719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-999473873813417658499148699966334000000000000)
      constant := (40197580431234720453644968331980194115514457871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 152 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (614149617796731846957/100000000000000000000)
  centralHi := (307074808898365923479/50000000000000000000)
  directionLo := (616179870004754582463/100000000000000000000)
  directionHi := (9627810468824290351/1562500000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree153.table
  base := (106124658048350885011208443684450045947607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-1003722243584285533304525751258214000000000000)
      constant := (40553275170230907366074575361666950037458162663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree153.table
  base := (26531164512073382803628893197779307041507/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-503023996729424119244975572150607000000000000)
      constant := (20368101643233010513466289671917022336806695526) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 153 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (616179870004754582463/100000000000000000000)
  centralHi := (9627810468824290351/1562500000000000000)
  directionLo := (61820345466381915477/10000000000000000000)
  directionHi := (618203454663819154771/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree154.table
  base := (6767432906432769954274018019494051347647/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-1313870651506312022346498202527953247000000000000)
      constant := (53441573431609592222458166300859401407167467574584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree154.table
  base := (27069731625718872927158857142877565608321/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-506311056552139409240376794318047000000000000)
      constant := (20639212250657733081206977939247994187077354978) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 154 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61820345466381915477/10000000000000000000)
  centralHi := (618203454663819154771/100000000000000000000)
  directionLo := (620220437036288859917/100000000000000000000)
  directionHi := (310110218518144429959/50000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree155.table
  base := (55226756786514206939162782266263103262949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-1322400525231260708630460665544599187000000000000)
      constant := (54148271849876031834368852826136724484055744072541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree155.table
  base := (55226756786493423397047789606156321560719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-509598116374854699235778016485487000000000000)
      constant := (20912122037893132394108462497509447415437667871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 155 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620220437036288859917/100000000000000000000)
  centralHi := (310110218518144429959/50000000000000000000)
  directionLo := (311115440663385270033/50000000000000000000)
  directionHi := (622230881326770540067/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree156.table
  base := (56324209629479407578687482012208061885183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (275940090)
      previous := (137970045)
      next := (137970045)
      square := (923074620214773936727435662813080000000000000)
      linear := (-147881155439578821657158125395693903000000000000)
      constant := (6095514401520965877652114819367191392948032963183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree156.table
  base := (56324209629461715207737391174601802656209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-512885176197569989231179238652927000000000000)
      constant := (21186831004940777703329761366579842524379721281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 156 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311115440663385270033/50000000000000000000)
  centralHi := (622230881326770540067/100000000000000000000)
  directionLo := (624234850705961507693/100000000000000000000)
  directionHi := (312117425352980753847/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree157.table
  base := (22972728712200937341951183430162334069881/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (993384324)
      previous := (496692162)
      next := (496692162)
      square := (3323068632773186172218768386127088000000000000)
      linear := (-535784109072463232479354236631156426800000000000)
      constant := (22230258689220626003002965933236165770885302942929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree157.table
  base := (57431821780487283018659883467581824760859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-516172236020285279226580460820367000000000000)
      constant := (21463339151802203725188562670190264578887953131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 157 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (624234850705961507693/100000000000000000000)
  centralHi := (312117425352980753847/50000000000000000000)
  directionLo := (4892440682295387959/781250000000000000)
  directionHi := (626232407333809658753/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree158.table
  base := (58549593239724419498774949163377571980873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-1347990146406106767482348054594537007000000000000)
      constant := (56296323177968550097501982384364773605138357389857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree158.table
  base := (58549593239711600158209177085361071124807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-519459295843000569221981682987807000000000000)
      constant := (21741646478478911350225797405898921603563077463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 158 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4892440682295387959/781250000000000000)
  centralHi := (626232407333809658753/100000000000000000000)
  directionLo := (628223612382010797597/100000000000000000000)
  directionHi := (314111806191005398799/50000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree159.table
  base := (7459690500910491473423171814768120256707/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (275940090)
      previous := (137970045)
      next := (137970045)
      square := (923074620214773936727435662813080000000000000)
      linear := (-150724446681228383751812279734575883000000000000)
      constant := (6335739886493718255974236332460603695051471349656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree159.table
  base := (29838762003636510208318173434643557363917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-522746355665715859217382905155247000000000000)
      constant := (22021752984972368373802239226697670000147590906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 159 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (628223612382010797597/100000000000000000000)
  centralHi := (314111806191005398799/50000000000000000000)
  directionLo := (63020852605586620973/10000000000000000000)
  directionHi := (630208526055866209731/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree160.table
  base := (60815614083316135211339399398730911251123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-1365049893856004140050272980627828887000000000000)
      constant := (57751654124480039853734592338464354273641689322107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree160.table
  base := (24326245633322739281784669094736921038957/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (1277611931093112715193682578288000000000000)
      linear := (-210413366195372459685113650929074800000000000)
      constant := (8921463468513604096163639112892431995302294813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 160 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63020852605586620973/10000000000000000000)
  centralHi := (630208526055866209731/100000000000000000000)
  directionLo := (632187207615522578149/100000000000000000000)
  directionHi := (12643744152310451563/2000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree161.table
  base := (619638634679533135490437590171862056881/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27594009000000000000000000000000000000000000000
      center := (496692162)
      previous := (248346081)
      next := (248346081)
      square := (1661534316386593086109384193063544000000000000)
      linear := (-274715953516190565266847088728894965400000000000)
      constant := (11697261723216385397434657576084696592036656518580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree161.table
  base := (484092683343323510917256869950823622487/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-529320475311146439208185349490127000000000000)
      constant := (22587363537415240795261926067477337839803466624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 161 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (632187207615522578149/100000000000000000000)
  centralHi := (12643744152310451563/2000000000000000000)
  directionLo := (634159715396615442787/100000000000000000000)
  directionHi := (158539928849153860697/25000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree162.table
  base := (126244544322649698637175841003248736543489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-307135475845755891692932868146915726000000000000)
      constant := (13161249434056154641433959341502486226491073817489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree162.table
  base := (63122272161318122371511746958310075472033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-532607535133861729203586571657567000000000000)
      constant := (22872867583367433037912066456985985590682798097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 162 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (634159715396615442787/100000000000000000000)
  centralHi := (158539928849153860697/25000000000000000000)
  directionLo := (636126106830336547959/100000000000000000000)
  directionHi := (15903152670758413699/2500000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree163.table
  base := (128581680327114587351063751809940588966243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-2781279030061700397804320739355533414000000000000)
      constant := (119939191271991677210597325256451614985899810038187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree163.table
  base := (64290840163551568824155733934791175967033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-535894594956577019198987793825007000000000000)
      constant := (23160170809141929873587081278754310585834253097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 163 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (636126106830336547959/100000000000000000000)
  centralHi := (15903152670758413699/2500000000000000000)
  directionLo := (12761728769258892153/2000000000000000000)
  directionHi := (638086438462944607651/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree164.table
  base := (4091847967173402244122305343693307864263/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-1399169388755798885186122832694412647000000000000)
      constant := (60718228164314770986385054525490635400139904005872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree164.table
  base := (26187826989907825621603074637756013128779/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (1277611931093112715193682578288000000000000)
      linear := (-215672661911716923677755606396978800000000000)
      constant := (9379709285896017943516210842119308743283216411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 164 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12761728769258892153/2000000000000000000)
  centralHi := (638086438462944607651/100000000000000000000)
  directionLo := (128008153194947648169/20000000000000000000)
  directionHi := (320020382987369120423/50000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree165.table
  base := (66658454095097372232234581640674991716637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (275940090)
      previous := (137970045)
      next := (137970045)
      square := (923074620214773936727435662813080000000000000)
      linear := (-156411029164527507941120588412339843000000000000)
      constant := (6830168893134759395551331283683407354028200758637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree165.table
  base := (26663381638037290574957760253745850885109/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (1277611931093112715193682578288000000000000)
      linear := (-216987485840803039675916095263954800000000000)
      constant := (9496069920065225175350741964868031732040121381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 165 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128008153194947648169/20000000000000000000)
  centralHi := (320020382987369120423/50000000000000000000)
  directionLo := (641989144198509086981/100000000000000000000)
  directionHi := (320994572099254543491/50000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree166.table
  base := (135715000049289147411857598876128209725839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4966921620)
      previous := (2483460810)
      next := (2483460810)
      square := (16615343163865930861093841930635440000000000000)
      linear := (-2832458272411392515508095517455409054000000000000)
      constant := (124458942515386596834585071282520319703328688898551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree166.table
  base := (67857500024641045892691913905928459304271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3194029827732781787984206445720000000000000)
      linear := (-545755774424722889185191460327327000000000000)
      constant := (24032875565412241171890116084933257024759011039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 166 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (641989144198509086981/100000000000000000000)
  centralHi := (320994572099254543491/50000000000000000000)
  directionLo := (128786325427498480631/20000000000000000000)
  directionHi := (160982906784373100789/25000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree167.table
  base := (34533352631765976504915973747640458809839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-1424759009930644944038010221744350467000000000000)
      constant := (62992081822759361053988904657970139713575653309102) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree167.table
  base := (138133410527057902338702319934017851171029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-1098085668494876358361185364989534000000000000)
      constant := (48654751020977618894866471155407713383073446661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 167 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128786325427498480631/20000000000000000000)
  centralHi := (160982906784373100789/25000000000000000000)
  directionLo := (645868267982831768257/100000000000000000000)
  directionHi := (322934133991415884129/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree168.table
  base := (140572139623745860061653965432475185311477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (1846149240429547873454871325626160000000000000)
      linear := (-318508640812354140071549485502443646000000000000)
      constant := (14168744829647589373206781310674171138640173793477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree168.table
  base := (140572139623740751671443498117435429721881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-1104659788140306938351987809324414000000000000)
      constant := (49247349270787942363465668811059664473919435529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 168 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell088.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645868267982831768257/100000000000000000000)
  centralHi := (322934133991415884129/50000000000000000000)
  directionLo := (161949779782643468259/25000000000000000000)
  directionHi := (647799119130573873037/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree169.table
  base := (35757796834889248049150931157200177892699/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (2483460810)
      previous := (1241730405)
      next := (1241730405)
      square := (8307671581932965430546920965317720000000000000)
      linear := (-1441818757380542316605935147777642347000000000000)
      constant := (64531280989660734489359422617291053038895474480582) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree169.table
  base := (143031187339552645742069283100978911528341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6388059655465563575968412891440000000000000)
      linear := (-1111233907785737518342790253659294000000000000)
      constant := (49843545880257808010791147653941031272404169669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 169 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell088.Kernel169
