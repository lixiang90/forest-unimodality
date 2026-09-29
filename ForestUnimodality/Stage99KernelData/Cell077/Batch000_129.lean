import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell077.Parameters
import ForestUnimodality.BinomialMassData.Q26_51.Batch000_049
import ForestUnimodality.BinomialMassData.Q26_51.Batch050_099
import ForestUnimodality.BinomialMassData.Q26_51.Batch100_149
import ForestUnimodality.BinomialMassData.Q3579_7004.Batch000_049
import ForestUnimodality.BinomialMassData.Q3579_7004.Batch050_099
import ForestUnimodality.BinomialMassData.Q3579_7004.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree000.table
  base := (6192504131438087216054100283/100000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (62)
      previous := (31)
      next := (31)
      square := (384372742624180113724108310000000000000)
      linear := (-9529314528547627640570061500000000000)
      constant := (309625206571904360802705014150000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree000.table
  base := (6192504131438087216054100283/100000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (62)
      previous := (31)
      next := (31)
      square := (384372742624180113724108310000000000000)
      linear := (-9529314528547627640570061500000000000)
      constant := (309625206571904360802705014150000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree001.table
  base := (87968756538695959535505776486440236378053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-1044142260528078041089457968081500000000000)
      constant := (457885943359375181414829942401571109638631706) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree001.table
  base := (351253108016518496281709952753180515281867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-2467232026034431147696770854507113000000000000)
      constant := (1077587680110835549856620998726785793534719503867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9997582471123184849/20000000000000000000)
  directionHi := (24993956177807962123/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree002.table
  base := (8348749692329837861480408276875854834717/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-4126997547934807405371586412403000000000000)
      constant := (545006680020118689614789109550528460627472925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree002.table
  base := (13003455363674905417006537606782005963707/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-2438015138160589592803155405378051500000000000)
      constant := (320209597253705825143994131203643065783853005656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9997582471123184849/20000000000000000000)
  centralHi := (24993956177807962123/50000000000000000000)
  directionLo := (70693583608029649531/100000000000000000000)
  directionHi := (17673395902007412383/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree003.table
  base := (130580748707443458659091448676416975098247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-685078952757050969840472987627000000000000)
      constant := (38265932238522287169066687036970505803393383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree003.table
  base := (130040669729149033539814749038954730372649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-7284828526607927223515850767005093000000000000)
      constant := (404333364788064208825386199134598516277272206649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70693583608029649531/100000000000000000000)
  centralHi := (17673395902007412383/25000000000000000000)
  directionLo := (86581603964226820861/100000000000000000000)
  directionHi := (43290801982113410431/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree004.table
  base := (1733857767220282591179558354000859771029/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-4102211800846055025878463682441500000000000)
      constant := (116952020381981424218496321056061906611160725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree004.table
  base := (86291999730519427197181476443091333460949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-9693626776894675261425390723254083000000000000)
      constant := (274537840823255732515742877737659858482603094949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86581603964226820861/100000000000000000000)
  centralHi := (43290801982113410431/50000000000000000000)
  directionLo := (99975824711231848491/100000000000000000000)
  directionHi := (24993956177807962123/25000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree005.table
  base := (30518402488419444647496119937731309488959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-5121568314285380687474798920561500000000000)
      constant := (85937443578051890221331817904784135980782359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree005.table
  base := (60747669929764438508455890474342900047651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-12102425027181423299334930679503073000000000000)
      constant := (201787722882997055683623055160365483388998013651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99975824711231848491/100000000000000000000)
  centralHi := (24993956177807962123/25000000000000000000)
  directionLo := (111776370080458847857/100000000000000000000)
  directionHi := (55888185040229423929/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree006.table
  base := (45228913434550485580222812305440126805839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-1364649961716601410904696479707000000000000)
      constant := (15166691602783128593372898365484196646887471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree006.table
  base := (11254783427191207739036620515567611811171/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-7255611638734085668622235317876031500000000000)
      constant := (80181859323793990523580623550620199511324194342) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111776370080458847857/100000000000000000000)
  centralHi := (55888185040229423929/50000000000000000000)
  directionLo := (122444878578225700663/100000000000000000000)
  directionHi := (15305609822278212583/12500000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree007.table
  base := (34868158116945236345961701883535014925737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-14320562682328064021334938793603000000000000)
      constant := (116332906910449202069360656541640573821841937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree007.table
  base := (3471169176766413154132684124565142159789/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-8460010763877459687577005296000526500000000000)
      constant := (68395837834484631267588040846383147635276168945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122444878578225700663/100000000000000000000)
  centralHi := (15305609822278212583/12500000000000000000)
  directionLo := (66127792326126339281/50000000000000000000)
  directionHi := (132255584652252678563/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree008.table
  base := (27622571106868682480814115058594959541087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-16359275709206715344527609269843000000000000)
      constant := (105307486059788166480939491539869489766367287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree008.table
  base := (27501217507589885633622121949628575637727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-19328819778041667413063550548250043000000000000)
      constant := (123945819470871355378483650494584776533846619727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66127792326126339281/50000000000000000000)
  centralHi := (132255584652252678563/100000000000000000000)
  directionLo := (70693583608029649531/50000000000000000000)
  directionHi := (141387167216059299063/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree009.table
  base := (22240208603741594143388920744999479872029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-2044220970676151851968919971787000000000000)
      constant := (11129739560862052639737139814482849683016381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree009.table
  base := (22142132035760244757573657650883208719671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-21737618028328415450973090504499033000000000000)
      constant := (118007203922446219369479206487534183317720005671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70693583608029649531/50000000000000000000)
  centralHi := (141387167216059299063/100000000000000000000)
  directionLo := (149963737066847772737/100000000000000000000)
  directionHi := (74981868533423886369/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree010.table
  base := (18035669655720571924914755629279312647619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-20436701762964017990912950222323000000000000)
      constant := (99130688998615442037230640934735492196457019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree010.table
  base := (8976743320024175798885860907265594225321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-12073208139307581744441315230374011500000000000)
      constant := (58444019795682098926129606352966615410428411321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149963737066847772737/100000000000000000000)
  centralHi := (74981868533423886369/50000000000000000000)
  directionLo := (19759457315077393009/12500000000000000000)
  directionHi := (158075658520619144073/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree011.table
  base := (7311443501798915747297909631805981677761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-11237707394921334657052810349281500000000000)
      constant := (50596211985579812137664381194126358343856361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree011.table
  base := (1819011516063207032429852848124237968713/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-13277607264450955763396085208498506500000000000)
      constant := (59706734015960922450442992478143120945248106852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19759457315077393009/12500000000000000000)
  centralHi := (158075658520619144073/100000000000000000000)
  directionLo := (8289557466837438329/5000000000000000000)
  directionHi := (165791149336748766581/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree012.table
  base := (11775731100967143923011583097245110346859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-2723791979635702293033143463867000000000000)
      constant := (11751633112798713225167314214487836890242251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree012.table
  base := (5856793882337954514207027501308728906223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-14482006389594329782350855186623001500000000000)
      constant := (62447799500891781217746236315894404635208624223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8289557466837438329/5000000000000000000)
  centralHi := (165791149336748766581/100000000000000000000)
  directionLo := (173163207928453641723/100000000000000000000)
  directionHi := (43290801982113410431/25000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree013.table
  base := (2338750683671373272456177675652394625481/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-13276420421799985980245480825521500000000000)
      constant := (56242726988658420680882212756520756841752162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree013.table
  base := (1162477834012090536846010396350232342069/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-15686405514737703801305625164747496500000000000)
      constant := (66455430887782399856824861891865030594063584276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173163207928453641723/100000000000000000000)
  centralHi := (43290801982113410431/25000000000000000000)
  directionLo := (22529247643946638149/12500000000000000000)
  directionHi := (180233981151573105193/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree014.table
  base := (3634978704963804025316333852369294652977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-14295776935239311641841816063641500000000000)
      constant := (60559332713252180777356781613458535392393177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree014.table
  base := (3610328356176128522963510330862355693631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-16890804639881077820260395142871991500000000000)
      constant := (71591443299371218755480594718659953169028339631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22529247643946638149/12500000000000000000)
  centralHi := (180233981151573105193/100000000000000000000)
  directionLo := (46759410378699673921/25000000000000000000)
  directionHi := (37407528302959739137/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree015.table
  base := (5457830716944795258806281365319640370121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-3403362988595252734097366955947000000000000)
      constant := (14611231348110514187841195864407376066964969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree015.table
  base := (2706833394515892847956818094759215211251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-18095203765024451839215165120996486500000000000)
      constant := (77760142097649053517049546246428521096910777251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46759410378699673921/25000000000000000000)
  centralHi := (37407528302959739137/20000000000000000000)
  directionLo := (193602352064976441253/100000000000000000000)
  directionHi := (96801176032488220627/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree016.table
  base := (1936389790680424962208108661783492010299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-16334489962117962965034486539881500000000000)
      constant := (71756733130167565555364912749442862718787699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree016.table
  base := (3833200429685444784911475825608062641413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-38599205780335651716339870198241963000000000000)
      constant := (169783084039048048333400725388876733666634899413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193602352064976441253/100000000000000000000)
  centralHi := (96801176032488220627/50000000000000000000)
  directionLo := (99975824711231848491/50000000000000000000)
  directionHi := (199951649422463696983/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree017.table
  base := (2479775214649945524187346350286409783879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1116)
      previous := (558)
      next := (558)
      square := (6918709367235242047033949580000000000000)
      linear := (-120095823360258052779452053827000000000000)
      constant := (543476498026194453384609481866577688054911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree017.table
  base := (488867166727552723349561054751590904399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1315516)
      previous := (657758)
      next := (657758)
      square := (8155620852999853652998130121580000000000000)
      linear := (-141896207718416608146191730638377000000000000)
      constant := (643128774582005078127784735641474639523844955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99975824711231848491/50000000000000000000)
  centralHi := (199951649422463696983/100000000000000000000)
  directionLo := (206105442646322579027/100000000000000000000)
  directionHi := (51526360661580644757/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree018.table
  base := (156390247113211870697077914642487424583/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (17918)
      previous := (8959)
      next := (8959)
      square := (111083722618388052866267301590000000000000)
      linear := (-2041466998777401587580795224013500000000000)
      constant := (9560153932294628478618513704584715462817948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree018.table
  base := (19053742765233799436493091372150935191/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-21708401140454573896079475055369971500000000000)
      constant := (101839477706379627179315954090290699712289318112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206105442646322579027/100000000000000000000)
  centralHi := (51526360661580644757/25000000000000000000)
  directionLo := (212080750824088948593/100000000000000000000)
  directionHi := (106040375412044474297/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree019.table
  base := (20548356295357756097247931045685790331/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-19392559502435939949823492254241500000000000)
      constant := (94254653268163549257988785143190314962603724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree019.table
  base := (13611763915542002012835669211510524769/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-22912800265597947915034245033494466500000000000)
      constant := (111579321496636445383512843171797493402261393845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212080750824088948593/100000000000000000000)
  centralHi := (106040375412044474297/50000000000000000000)
  directionLo := (4357845167133960689/2000000000000000000)
  directionHi := (217892258356698034451/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree020.table
  base := (-798898450762620990566462639690654400937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-40823832031750531222839654984723000000000000)
      constant := (206296279183317194475590240784124607903162863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree020.table
  base := (-206017575715116438728747717943799513087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-24117199390741321933989015011618961500000000000)
      constant := (122123370089470260173865843048090852998151489826) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4357845167133960689/2000000000000000000)
  centralHi := (217892258356698034451/100000000000000000000)
  directionLo := (111776370080458847857/50000000000000000000)
  directionHi := (44710548032183539143/20000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree021.table
  base := (-1654100061660067690041505934141881346211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-4762505006514353616225813940107000000000000)
      constant := (25044857933849577331412579646474996290945021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree021.table
  base := (-1676467743289836480548154116455974462073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-50643197031769391905887569979486913000000000000)
      constant := (266896203923788930532469238094872331343309719927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111776370080458847857/50000000000000000000)
  centralHi := (44710548032183539143/20000000000000000000)
  directionLo := (229073392202428265323/100000000000000000000)
  directionHi := (57268348050607066331/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree022.table
  base := (-2414089601469439492406034410497587656467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-44901258085507833869224995937203000000000000)
      constant := (245798154118931063324730630764531774505529333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree022.table
  base := (-1216962902738220808128314414260206691857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-26525997641028069971898554967867951500000000000)
      constant := (145533816335397531067353176386238178772559746143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229073392202428265323/100000000000000000000)
  centralHi := (57268348050607066331/25000000000000000000)
  directionLo := (117232045956726633819/50000000000000000000)
  directionHi := (234464091913453267639/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree023.table
  base := (-1544847472788101063353115296725710780673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-23469985556193242596208833206721500000000000)
      constant := (133725707011147100070196680938083426259469527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree023.table
  base := (-776813188380698139370460189206304762869/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-27730396766171443990853324945992446500000000000)
      constant := (158363944135706175556754111670786690281477766262) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117232045956726633819/50000000000000000000)
  centralHi := (234464091913453267639/100000000000000000000)
  directionLo := (47946721171931246523/20000000000000000000)
  directionHi := (29966700732457029077/12500000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree024.table
  base := (-922512206053360053719786503286700951067/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (17918)
      previous := (8959)
      next := (8959)
      square := (111083722618388052866267301590000000000000)
      linear := (-2721038007736952028645018716093500000000000)
      constant := (16129985937966630740446841062404286850283274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree024.table
  base := (-3705562144728611338266939941769616076797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-57869591782629636019616189848233883000000000000)
      constant := (343849028549846292412776517735149337338924321203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47946721171931246523/20000000000000000000)
  centralHi := (29966700732457029077/12500000000000000000)
  directionLo := (122444878578225700663/50000000000000000000)
  directionHi := (244889757156451401327/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree025.table
  base := (-2111433412918309825413683001753738905419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-25508698583071893919401503682961500000000000)
      constant := (157221542228336928048819669026163525107005181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree025.table
  base := (-2118275395486279490316360729105046041649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-30139195016458192028762864902241436500000000000)
      constant := (186203727536590049730167228116449580981258124351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122444878578225700663/50000000000000000000)
  centralHi := (244889757156451401327/100000000000000000000)
  directionLo := (62484890444519905307/25000000000000000000)
  directionHi := (249939561778079621229/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree026.table
  base := (-2347336947012244860057704337886104764563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-26528055096511219580997838921081500000000000)
      constant := (169872227681934690778714323527992241507371637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree026.table
  base := (-4706725378803658283867722330950571880687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-62687188283203132095435269760731863000000000000)
      constant := (402383218333947781804540585028236996163241777313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62484890444519905307/25000000000000000000)
  centralHi := (249939561778079621229/100000000000000000000)
  directionLo := (254889340545051468991/100000000000000000000)
  directionHi := (3982645946016429203/1562500000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree027.table
  base := (-5110991506848173336429314400142967943893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-6121647024433454498354260924267000000000000)
      constant := (40692166471169215445434852792372682264214923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree027.table
  base := (-204863592645791714806220055095258617839/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-65095986533489880133344809716980853000000000000)
      constant := (433759443344953870336896490603485025561175204025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254889340545051468991/100000000000000000000)
  centralHi := (3982645946016429203/1562500000000000000)
  directionLo := (51948962378536092517/20000000000000000000)
  directionHi := (129872405946340231293/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree028.table
  base := (-2738246897266249206832166801527477161027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-28566768123389870904190509397321500000000000)
      constant := (196943027836959875524026437959639031904168773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree028.table
  base := (-2742900752356138021177488941205289272157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-33752392391888314085627174836614921500000000000)
      constant := (233260925253939373377261711786098316386277365843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51948962378536092517/20000000000000000000)
  centralHi := (129872405946340231293/50000000000000000000)
  directionLo := (2116089354436042857/800000000000000000)
  directionHi := (132255584652252678563/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree029.table
  base := (-289756925642058459220037516766886703341/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-29586124636829196565786844635441500000000000)
      constant := (211351916770659211482952465301774276846100590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree029.table
  base := (-1160660486580169527864726026096641257161/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-69913583034063376209163889629478833000000000000)
      constant := (500658353682362150316744516656784258544515584195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2116089354436042857/800000000000000000)
  centralHi := (132255584652252678563/50000000000000000000)
  directionLo := (134596573199793459891/50000000000000000000)
  directionHi := (269193146399586919783/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree030.table
  base := (-6070277325087997535141159488877487891711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-6801218033393004939418484416347000000000000)
      constant := (50297123796271081116186287763374405999295521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree030.table
  base := (-6077429536589627033494570402916993883499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-72322381284350124247073429585727823000000000000)
      constant := (536158721819661765148560475169615721336198182501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134596573199793459891/50000000000000000000)
  centralHi := (269193146399586919783/100000000000000000000)
  directionLo := (136897535998810233711/50000000000000000000)
  directionHi := (273795071997620467423/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree031.table
  base := (-1260949774707223574622397609622121232661/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-63249675327415695777959030223363000000000000)
      constant := (483789514240757259694171917133222313369243695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree031.table
  base := (-6311007811286649782293751238367224437999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-74731179534636872284982969541976813000000000000)
      constant := (573014293480724958722867771201221384505870628001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136897535998810233711/50000000000000000000)
  centralHi := (273795071997620467423/100000000000000000000)
  directionLo := (278320916985868876671/100000000000000000000)
  directionHi := (2174382163952100599/781250000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree032.table
  base := (-6500957437083178945341895451984910038537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-65288388354294347101151700699603000000000000)
      constant := (516043780234858227520369369191403248989765263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree032.table
  base := (-6506428978436719150342920690479520741419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-77139977784923620322892509498225803000000000000)
      constant := (611217735645210242785532860597375714927288604581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278320916985868876671/100000000000000000000)
  centralHi := (2174382163952100599/781250000000000000)
  directionLo := (452438935091389757/160000000000000000)
  directionHi := (141387167216059299063/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree033.table
  base := (-52038589574106995773214634848107142977/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (17918)
      previous := (8959)
      next := (8959)
      square := (111083722618388052866267301590000000000000)
      linear := (-3740394521176277690241353954213500000000000)
      constant := (30523978630162552153944237077622410283497408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree033.table
  base := (-3332859001444374595654016074473023553561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-39774388017605184180401024727237396500000000000)
      constant := (325381419884432940999550938299664573561758420439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452438935091389757/160000000000000000)
  centralHi := (141387167216059299063/50000000000000000000)
  directionLo := (143579347048244018119/50000000000000000000)
  directionHi := (287158694096488036239/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree034.table
  base := (-3393209944508577728002880151860738305859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (558)
      previous := (279)
      next := (279)
      square := (3459354683617621023516974790000000000000)
      linear := (-120010059529501124130686923273500000000000)
      constant := (1010291579621659257869891878467253355247269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree034.table
  base := (-1697647341702748388609041160807919711241/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (657758)
      previous := (328879)
      next := (328879)
      square := (4077810426499926826499065060790000000000000)
      linear := (-141795111220583246364552922855923500000000000)
      constant := (1196616521189705066620639490753742809566888462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143579347048244018119/50000000000000000000)
  centralHi := (287158694096488036239/100000000000000000000)
  directionLo := (291477112269339480869/100000000000000000000)
  directionHi := (29147711226933948087/10000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree035.table
  base := (-859857473828779093475546169944384603031/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-35702263717465150535364856064161500000000000)
      constant := (309795366496638829885213365713113622590065476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree035.table
  base := (-6882494692686357979670142280532429518773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-84366372535783864436621129366972773000000000000)
      constant := (733857813405576970826845669110891220563012463227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291477112269339480869/100000000000000000000)
  centralHi := (29147711226933948087/10000000000000000000)
  directionLo := (73933119421603718487/25000000000000000000)
  directionHi := (295732477686414873949/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree036.table
  base := (-6939496773809287514607087998165934274869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-8160360051312105821546931400507000000000000)
      constant := (72928332916904327123008917438202044994562859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree036.table
  base := (-1388532610633959832065940546727166383229/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-86775170786070612474530669323221763000000000000)
      constant := (777399463904659039082774997940508528709267513855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73933119421603718487/25000000000000000000)
  centralHi := (295732477686414873949/100000000000000000000)
  directionLo := (149963737066847772737/50000000000000000000)
  directionHi := (11997098965347821819/4000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree037.table
  base := (-696937914958433865137549164489911013811/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-37740976744343801858557526540401500000000000)
      constant := (347119298070456912456481512312761707265387945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree037.table
  base := (-6972135094942376192101024254753829005141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-89183969036357360512440209279470753000000000000)
      constant := (822266110121130959406084693937055199016408688859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149963737066847772737/50000000000000000000)
  centralHi := (11997098965347821819/4000000000000000000)
  directionLo := (304064600244571958749/100000000000000000000)
  directionHi := (243251680195657567/80000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree038.table
  base := (-139387897826394425433139268640320401061/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-38760333257783127520153861778521500000000000)
      constant := (366619611520440833278869145472165165921008475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree038.table
  base := (-6971791928011379709495840048561550405221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-91592767286644108550349749235719743000000000000)
      constant := (868455050570829268704071148583264079396042008779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304064600244571958749/100000000000000000000)
  centralHi := (243251680195657567/80000000000000000)
  directionLo := (19259136681509044789/6250000000000000000)
  directionHi := (2465169495233157733/800000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree039.table
  base := (-3470148079613274729693891778405507737117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (17918)
      previous := (8959)
      next := (8959)
      square := (111083722618388052866267301590000000000000)
      linear := (-4419965530135828131305577446293500000000000)
      constant := (42964162254629631183838210617059808263973187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree039.table
  base := (-1735594896135580825842414141896685095083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-47000782768465428294129644595984366500000000000)
      constant := (457981998959194235070828894120089326703580853834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19259136681509044789/6250000000000000000)
  centralHi := (2465169495233157733/800000000000000000)
  directionLo := (312174412604936005567/100000000000000000000)
  directionHi := (4877725196952125087/1562500000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree040.table
  base := (-860340009133955906693553607634251538199/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-40799046284661778843346532254761500000000000)
      constant := (407292015809877699920811652424133246996577604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree040.table
  base := (-1721132431814630476974602379112159323417/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-48205181893608802313084414574108861500000000000)
      constant := (482395507742633608703673129930750315804488309166) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312174412604936005567/100000000000000000000)
  centralHi := (4877725196952125087/1562500000000000000)
  directionLo := (63230263408247657629/20000000000000000000)
  directionHi := (158075658520619144073/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree041.table
  base := (-3398603153679252975466876549368308413353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-41818402798101104504942867492881500000000000)
      constant := (428462576228382100646190708776962029816868847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree041.table
  base := (-6798777182786934675348139516160824458637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-98819162037504352664078369104466713000000000000)
      constant := (1014934463492492427113329730637161746548994499363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63230263408247657629/20000000000000000000)
  centralHi := (158075658520619144073/50000000000000000000)
  directionLo := (80019703295728322451/25000000000000000000)
  directionHi := (64015762636582657961/20000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree042.table
  base := (-6684211995200705748539094681646364020953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-9519502069231206703675378384667000000000000)
      constant := (100041899343459038174330806001648200797944583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree042.table
  base := (-1671393696727900226541984346976475854293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-50613980143895550350993954530357851500000000000)
      constant := (533196476772548699490195993830162660358523615414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80019703295728322451/25000000000000000000)
  centralHi := (64015762636582657961/20000000000000000000)
  directionLo := (64791739606297050119/20000000000000000000)
  directionHi := (80989674507871312649/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree043.table
  base := (-6544124352627856097094445960170061860129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-87714231649959511656271075938243000000000000)
      constant := (944938849373963812490062104127691669101804471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree043.table
  base := (-6545305953934915417592873489601996901039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-103636758538077848739897449016964693000000000000)
      constant := (1119165310094447576196495487978544031899417524961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64791739606297050119/20000000000000000000)
  centralHi := (80989674507871312649/25000000000000000000)
  directionLo := (327792662230147831537/100000000000000000000)
  directionHi := (163896331115073915769/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree044.table
  base := (-99644865187983414448472407499053525961/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-44876472338419081489731873207241500000000000)
      constant := (495304782598526332550520777443354776927214048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree044.table
  base := (-199321728721868395770321064695707998111/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-53022778394182298388903494486606841500000000000)
      constant := (586625268904281780031807997142508041813338814224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327792662230147831537/100000000000000000000)
  centralHi := (163896331115073915769/50000000000000000000)
  directionLo := (331582298673497533161/100000000000000000000)
  directionHi := (165791149336748766581/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree045.table
  base := (-6183930880090406312663848212314764387387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-10199073078190757144739601876747000000000000)
      constant := (115265390992578004713027854784131033092045157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree045.table
  base := (-3092408874750944113502234932195970412791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-54227177519325672407858264464731336500000000000)
      constant := (614323896972327583343417544441710646268412381209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331582298673497533161/100000000000000000000)
  centralHi := (165791149336748766581/50000000000000000000)
  directionLo := (83832277560344135893/25000000000000000000)
  directionHi := (335329110241376543573/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree046.table
  base := (-1491084552585904868361730623693310903541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-46915185365297732812924543683481500000000000)
      constant := (542637549239940635523130601123761396679779718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree046.table
  base := (-745638246702102671934629028628091032009/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-55431576644469046426813034442855831500000000000)
      constant := (642678182478491727849103281585759684821077495964) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83832277560344135893/25000000000000000000)
  centralHi := (335329110241376543573/100000000000000000000)
  directionLo := (1695172583816659671/500000000000000000)
  directionHi := (339034516763331934201/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree047.table
  base := (-2859346351140149736130253262121428667423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-47934541878737058474520878921601500000000000)
      constant := (567134392677538792728532172228065164036032777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree047.table
  base := (-2859678520607672850818739994870152221137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-56635975769612420445767804420980326500000000000)
      constant := (671687823345377117275610340430282698919841736863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1695172583816659671/500000000000000000)
  centralHi := (339034516763331934201/100000000000000000000)
  directionLo := (21418741331576406591/6250000000000000000)
  directionHi := (342699861305222505457/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree048.table
  base := (-1361790801610919765423876433356474209211/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (17918)
      previous := (8959)
      next := (8959)
      square := (111083722618388052866267301590000000000000)
      linear := (-5439322043575153792901912684413500000000000)
      constant := (65798285576584890958898398591807957907076042) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree048.table
  base := (-2723868896485535715012689781104700931013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-57840374894755794464722574399104821500000000000)
      constant := (701352563806147686811914453390273247840813210987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21418741331576406591/6250000000000000000)
  centralHi := (342699861305222505457/100000000000000000000)
  directionLo := (346326415856907283447/100000000000000000000)
  directionHi := (43290801982113410431/12500000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree049.table
  base := (-5149892747563149156705418685001045163447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-99946509811231419595427098795683000000000000)
      constant := (1235575791542911480685787643075234281529874353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree049.table
  base := (-5150389491575895384282564556571805473593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-118089548039798336967354688754458633000000000000)
      constant := (1463344374610052254562848555440940472346158388407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346326415856907283447/100000000000000000000)
  centralHi := (43290801982113410431/12500000000000000000)
  directionLo := (8747884662232786743/2500000000000000000)
  directionHi := (349915386489311469721/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree050.table
  base := (-2413501237245986580770539987688796539941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-50992611419055035459309884635961500000000000)
      constant := (643944211870030288809728664469471440199613459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree050.table
  base := (-2413715871452137692481312800762575599553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-60249173145042542502632114355353811500000000000)
      constant := (762646510486147091908002248710284873699194902447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8747884662232786743/2500000000000000000)
  centralHi := (349915386489311469721/100000000000000000000)
  directionLo := (44183489755018530957/12500000000000000000)
  directionHi := (353467918040148247657/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree051.table
  base := (-4478595006028211131750024179137728840841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (124)
      previous := (62)
      next := (62)
      square := (768745485248360227448216620000000000000)
      linear := (-39993823861971827082588404363000000000000)
      constant := (515688877377347779260554054138862271159159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree051.table
  base := (-2239482908030871582509823263592472735043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (657758)
      previous := (328879)
      next := (328879)
      square := (4077810426499926826499065060790000000000000)
      linear := (-212642118581958188656009980392658500000000000)
      constant := (2748357709702149363295030759069578456753928813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44183489755018530957/12500000000000000000)
  centralHi := (353467918040148247657/100000000000000000000)
  directionLo := (17849254918995197249/5000000000000000000)
  directionHi := (356985098379903944981/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree052.table
  base := (-4104757265014109183103551547496855160389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-106062648891867373565005110224403000000000000)
      constant := (1395830604411861787250397788750536679727828211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree052.table
  base := (-513134681808558652200746506048963947993/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-62657971395329290540541654311602801500000000000)
      constant := (826558658713642356458121408678917257445958056028) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17849254918995197249/5000000000000000000)
  centralHi := (356985098379903944981/100000000000000000000)
  directionLo := (72093592460629242077/20000000000000000000)
  directionHi := (180233981151573105193/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree053.table
  base := (-3705562878977976652695342998989427025269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-108101361918746024888197780700643000000000000)
      constant := (1451459735295000085214766746675902500307275331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree053.table
  base := (-46322990700024573845428884382318260317/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-63862370520472664559496424289727296500000000000)
      constant := (859496241022728137911407441915878294011992707320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72093592460629242077/20000000000000000000)
  centralHi := (180233981151573105193/50000000000000000000)
  directionLo := (177694089396780907/48828125000000000)
  directionHi := (363917495084607297537/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree054.table
  base := (-3281074213612666705525055785291419770903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-12237786105069408467932272352987000000000000)
      constant := (167577111166081039629738206675518779686209033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree054.table
  base := (-3281312688261961281849651809578601291793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-130133539291232077156902388535703583000000000000)
      constant := (1786176061602634786913195794605952548360761370207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (177694089396780907/48828125000000000)
  centralHi := (363917495084607297537/100000000000000000000)
  directionLo := (367334635734677101989/100000000000000000000)
  directionHi := (36733463573467710199/10000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree055.table
  base := (-2831344095245601177516734618133290932529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-112178787972503327534583121653123000000000000)
      constant := (1566033262609771977413790688666625310284492071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree055.table
  base := (-707887448723266532292540747605421957519/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-66271168770759412597405964245976286500000000000)
      constant := (927333948266476912931975829197304814845649576962) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367334635734677101989/100000000000000000000)
  centralHi := (36733463573467710199/10000000000000000000)
  directionLo := (9268006999619735361/2500000000000000000)
  directionHi := (370720279984789414441/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree056.table
  base := (-235641726986682364654286110989428447511/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-57108750499690989428887896064681500000000000)
      constant := (812488702627903922053580453881486483040119445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree056.table
  base := (-2356594640325978832449473259042357753439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-134951135791805573232721468448201563000000000000)
      constant := (1924467851734824807002554865934564730085598272561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9268006999619735361/2500000000000000000)
  centralHi := (370720279984789414441/100000000000000000000)
  directionLo := (46759410378699673921/12500000000000000000)
  directionHi := (374075283029597391369/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree057.table
  base := (-928165819503323795112199654145705690593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (17918)
      previous := (8959)
      next := (8959)
      square := (111083722618388052866267301590000000000000)
      linear := (-6458678557014479454498247922533500000000000)
      constant := (93612573880608700632914577215588891055418623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree057.table
  base := (-1856484533037617247395924219574764949381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-137359934042092321270631008404450553000000000000)
      constant := (1995575812820420191706485786159200929590432904619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46759410378699673921/12500000000000000000)
  centralHi := (374075283029597391369/100000000000000000000)
  directionLo := (4717505775621566033/1250000000000000000)
  directionHi := (377400462049725282641/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree058.table
  base := (-332779826648047474437892725543072814927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-59147463526569640752080566540921500000000000)
      constant := (873089976446451924120455684203406935216749746) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree058.table
  base := (-66562553064160800507672262356676274951/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-69884366146189534654270274180349771500000000000)
      constant := (1033995841470058921163046247730243720093239590490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4717505775621566033/1250000000000000000)
  centralHi := (377400462049725282641/100000000000000000000)
  directionLo := (380696598536181923247/100000000000000000000)
  directionHi := (23793537408511370203/6250000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree059.table
  base := (-780807465692273074523516475754117796709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-120333640080017932827353803558083000000000000)
      constant := (1808438203652477547315964678682065539610759891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree059.table
  base := (-39046048502422886739280681196865208397/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-71088765271332908673225044158474266500000000000)
      constant := (1070857690046882455490486725913782276741895896030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380696598536181923247/100000000000000000000)
  centralHi := (23793537408511370203/6250000000000000000)
  directionLo := (383964440435167917447/100000000000000000000)
  directionHi := (47995555054395989681/12500000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree060.table
  base := (-205419149638698702974670672360986179837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-13596928122988509350060719337147000000000000)
      constant := (207977891357775743633523372911007674994027107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree060.table
  base := (-205516903562651333867480890385736191209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-144586328792952565384359628273197523000000000000)
      constant := (2216746834854131692315864634662515447452017014791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383964440435167917447/100000000000000000000)
  centralHi := (47995555054395989681/12500000000000000000)
  directionLo := (193602352064976441253/50000000000000000000)
  directionHi := (387204704129952882507/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree061.table
  base := (395026131733357340496917513526098113569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-124411066133775235473739144510563000000000000)
      constant := (1936268357850334991943637075523179381193392969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree061.table
  base := (78988393203497815446545990535507296361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-146995127043239313422269168229446513000000000000)
      constant := (2293085988439366528696332956876530515030750611805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193602352064976441253/50000000000000000000)
  centralHi := (387204704129952882507/100000000000000000000)
  directionLo := (78083615254939903431/20000000000000000000)
  directionHi := (97604519068674879289/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree062.table
  base := (255127963288881052370514828974569232529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-63224889580326943398465907493401500000000000)
      constant := (1000920083780657206235117268337003709147615858) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree062.table
  base := (510219703151671628319238786504859781393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-74701962646763030730089354092847751500000000000)
      constant := (1185366395540474839036082350434206008344610719393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78083615254939903431/20000000000000000000)
  centralHi := (97604519068674879289/25000000000000000000)
  directionLo := (393605215493532083847/100000000000000000000)
  directionHi := (49200651936691510481/12500000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree063.table
  base := (1671024017423933409439071148700780618049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-14276499131948059791124942829227000000000000)
      constant := (229835157216243632480799980071580525598616161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree063.table
  base := (835480836987067805936849971813341088089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-75906361771906404749044124070972246500000000000)
      constant := (1224843600320922949578026333993682290089421962089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393605215493532083847/100000000000000000000)
  centralHi := (49200651936691510481/12500000000000000000)
  directionLo := (396766753956758035687/100000000000000000000)
  directionHi := (49595844244594754461/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree064.table
  base := (2346550768717632180728519945734007865857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-130527205214411189443317155939283000000000000)
      constant := (2136297069167979533386710762028646154459094057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree064.table
  base := (2346497133170917680797260397252966542497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-154221521794099557535997788098193483000000000000)
      constant := (2529949181446500020104123671070384984672262344497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396766753956758035687/100000000000000000000)
  centralHi := (49595844244594754461/12500000000000000000)
  directionLo := (79980659768985478793/20000000000000000000)
  directionHi := (199951649422463696983/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree065.table
  base := (1523541032529515408037004576381660353731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-66282959120644920383254913207761500000000000)
      constant := (1102591052053745612410070726694853698580054331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree065.table
  base := (1523517966196272830812579402005062015227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-78315160022193152786953664027221236500000000000)
      constant := (1305759351645099841259482081967632888393747997227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79980659768985478793/20000000000000000000)
  centralHi := (199951649422463696983/50000000000000000000)
  directionLo := (201507716855166645209/50000000000000000000)
  directionHi := (403015433710333290419/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree066.table
  base := (3772609400870931023191056966025329898113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-14956070140907610232189166321307000000000000)
      constant := (252796833071302385985473328617313320340554657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree066.table
  base := (1886284865462602714117665788753852769393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-79519559147336526805908434005345731500000000000)
      constant := (1347197870300153995788034886752035126594811707393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201507716855166645209/50000000000000000000)
  centralHi := (403015433710333290419/100000000000000000000)
  directionLo := (203051859872300102203/50000000000000000000)
  directionHi := (406103719744600204407/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree067.table
  base := (4523125571968122105521195599213278028553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-136643344295047143412895167368003000000000000)
      constant := (2346265231032584547512317699814799736152266353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree067.table
  base := (2261545733605950581577676798690737250943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-80723958272479900824863203983470226500000000000)
      constant := (1389290135863042068271037113442668272102128488943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203051859872300102203/50000000000000000000)
  centralHi := (406103719744600204407/100000000000000000000)
  directionLo := (409168696960157895569/100000000000000000000)
  directionHi := (40916869696015789557/10000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree068.table
  base := (2649312238246692512650477941416167891633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (558)
      previous := (279)
      next := (279)
      square := (3459354683617621023516974790000000000000)
      linear := (-239934355228245319612608715993500000000000)
      constant := (4184192540500259202477667641620745511024697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree068.table
  base := (1324648790683105482202333257245617772923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (657758)
      previous := (328879)
      next := (328879)
      square := (4077810426499926826499065060790000000000000)
      linear := (-283489125943333130947467037929393500000000000)
      constant := (4955142350064669848031416785706123017905880214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409168696960157895569/100000000000000000000)
  centralHi := (40916869696015789557/10000000000000000000)
  directionLo := (206105442646322579027/50000000000000000000)
  directionHi := (82442177058529031611/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree069.table
  base := (6099100946300371699071662546177757866417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-15635641149867160673253389813387000000000000)
      constant := (276862850703229848562611837144743372023394513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree069.table
  base := (6099075755949943231051104151436292840907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-166265513045533297725545487879438433000000000000)
      constant := (2950871744915516133000447161016111294786513702907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206105442646322579027/50000000000000000000)
  centralHi := (82442177058529031611/20000000000000000000)
  directionLo := (415230785630616511313/100000000000000000000)
  directionHi := (207615392815308255657/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree070.table
  base := (10819610318947873891859366722257626603/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-71379741687841548691236589398361500000000000)
      constant := (1283086161703540693895006467262699467774208960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree070.table
  base := (3462264480857482446126001706822014614597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-84337155647910022881727513917843711500000000000)
      constant := (1519489329161111183181414671721460152380369016597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415230785630616511313/100000000000000000000)
  centralHi := (207615392815308255657/50000000000000000000)
  directionLo := (41822888077832662109/10000000000000000000)
  directionHi := (418228880778326621091/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree071.table
  base := (7774969742612335654527150886209821370077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-144798196402561748705665849272963000000000000)
      constant := (2641683280000345095780050284914909745383570277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree071.table
  base := (3887475576111947776853364670832621693043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-85541554773053396900682283895968206500000000000)
      constant := (1564196503717324216669961818197081640443491531043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41822888077832662109/10000000000000000000)
  centralHi := (418228880778326621091/100000000000000000000)
  directionLo := (421205636356832815129/100000000000000000000)
  directionHi := (42120563635683281513/10000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree072.table
  base := (1730071044364664032042787653294450266371/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-16315212158826711114317613305467000000000000)
      constant := (302033168660210117917200957212914480634906095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree072.table
  base := (8650339256227880199263290023366128538391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-173491907796393541839274107748185403000000000000)
      constant := (3219114782836342273203353016515246059464835344391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (421205636356832815129/100000000000000000000)
  centralHi := (42120563635683281513/10000000000000000000)
  directionLo := (424161501648177897187/100000000000000000000)
  directionHi := (106040375412044474297/25000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree073.table
  base := (4775352191224261813131435733351636280911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-74437811228159525676025595112721500000000000)
      constant := (1398009015157425596636489437532764605966649511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree073.table
  base := (4775345336847018013475619865351890954603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-87950353023340144938591823852217196500000000000)
      constant := (1655571988277800233624696647616771686268703752603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424161501648177897187/100000000000000000000)
  centralHi := (106040375412044474297/25000000000000000000)
  directionLo := (213548455193493474363/50000000000000000000)
  directionHi := (427096910386986948727/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree074.table
  base := (1309501871534276716916555084737140054821/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-75457167741598851337621930350841500000000000)
      constant := (1437420905630608787038577899174791205130357684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree074.table
  base := (2095200640710034788873941533033630980673/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-178309504296967037915093187660683383000000000000)
      constant := (3404480581843933482648554310279952612601871993365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213548455193493474363/50000000000000000000)
  centralHi := (427096910386986948727/100000000000000000000)
  directionLo := (86002456300685435563/20000000000000000000)
  directionHi := (53751535187928397227/12500000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree075.table
  base := (11426285083904491603683827623517009348493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-16994783167786261555381836797547000000000000)
      constant := (328307761757761496741192746492346415701714477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree075.table
  base := (11426274982507242677963061485522285447023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-180718302547253785953002727616932373000000000000)
      constant := (3499124592988495224907063219340608912702857965023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86002456300685435563/20000000000000000000)
  centralHi := (53751535187928397227/12500000000000000000)
  directionLo := (432908019821134104309/100000000000000000000)
  directionHi := (43290801982113410431/10000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree076.table
  base := (6200756551003963202683494804298825139007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-77495880768477502660814600827081500000000000)
      constant := (1517901079894640915737709787130265244186557207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree076.table
  base := (99212035466089757885700451057802077427/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-183127100797540533990912267573181363000000000000)
      constant := (3595076005153269983760368058810715021399157428375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432908019821134104309/100000000000000000000)
  centralHi := (43290801982113410431/10000000000000000000)
  directionLo := (435784516713396068901/100000000000000000000)
  directionHi := (217892258356698034451/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree077.table
  base := (13401697658633314834555582267021121439487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-157030474563833656644821872130403000000000000)
      constant := (3117938719611461576692756044141547936864105687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree077.table
  base := (837605638789782675090637075119071338599/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-92767949523913641014410903764715176500000000000)
      constant := (1846167407122304044325757713559016714495726980792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435784516713396068901/100000000000000000000)
  centralHi := (217892258356698034451/50000000000000000000)
  directionLo := (219321075360304188947/50000000000000000000)
  directionHi := (87728430144121675579/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree078.table
  base := (577073503814415827961131439893946177597/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-17674354176745811996446060289627000000000000)
      constant := (355686614697037956329086275087869761133138325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree078.table
  base := (14426831214453452784496290307183555756379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-187944697298114030066731347485679343000000000000)
      constant := (3790901016797377451988782329682680400632613770379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219321075360304188947/50000000000000000000)
  centralHi := (87728430144121675579/20000000000000000000)
  directionLo := (441481288131754974921/100000000000000000000)
  directionHi := (220740644065877487461/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree079.table
  base := (967308245702506933248622644964285942829/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-80553950308795479645603606541441500000000000)
      constant := (1642762297611736711125357751010747861898385832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree079.table
  base := (3095385291617764829444376768212113119947/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-190353495548400778104640887441928333000000000000)
      constant := (3890774609878570430290612825690130272189353109735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441481288131754974921/100000000000000000000)
  centralHi := (220740644065877487461/50000000000000000000)
  directionLo := (88860456706489280851/20000000000000000000)
  directionHi := (13884446360388950133/3125000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree080.table
  base := (16551979835638895461706779008127840183501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-163146613644469610614399883559123000000000000)
      constant := (3370973906301379119808087061215980512317286101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree080.table
  base := (165519751418569697805401936015023462817/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-96381146899343763071275213699088661500000000000)
      constant := (1995977795502844979257439868977083567601019240850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88860456706489280851/20000000000000000000)
  centralHi := (13884446360388950133/3125000000000000000)
  directionLo := (447105480321835391429/100000000000000000000)
  directionHi := (44710548032183539143/10000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree081.table
  base := (2206497575654614390721242287296082759759/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (17918)
      previous := (8959)
      next := (8959)
      square := (111083722618388052866267301590000000000000)
      linear := (-9176962592852681218755141890853500000000000)
      constant := (192084859093206878387631790799295271670281404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree081.table
  base := (17651976580472112923352017460409424884503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-195171092048974274180459967354426313000000000000)
      constant := (4094443958077649159826276151650835877605311082503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447105480321835391429/100000000000000000000)
  centralHi := (44710548032183539143/10000000000000000000)
  directionLo := (449891211200543318211/100000000000000000000)
  directionHi := (112472802800135829553/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree082.table
  base := (3755386728908978857534358766334795149433/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-167224039698226913260785224511603000000000000)
      constant := (3545185265803639889828045845357100010918376165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree082.table
  base := (73347383570181216156484809336981796449/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-98789945149630511109184753655337651500000000000)
      constant := (2099119854658132994315167338190666466436487097472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449891211200543318211/100000000000000000000)
  centralHi := (112472802800135829553/25000000000000000000)
  directionLo := (14145618707236255673/3125000000000000000)
  directionHi := (452659798631560181537/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree083.table
  base := (4981709612350337779046349550574649080577/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-84631376362552782291988947493921500000000000)
      constant := (1816973655683901671058543301961496324517161554) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree083.table
  base := (19926835491533743710374101388850358263977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-199988688549547770256279047266924293000000000000)
      constant := (4303342843216728570149775719004060801287711745977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14145618707236255673/3125000000000000000)
  centralHi := (452659798631560181537/100000000000000000000)
  directionLo := (455411555275925505339/100000000000000000000)
  directionHi := (22770577763796275267/5000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree084.table
  base := (21101694592994372187984743640990194314513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-19033496194664912878574507273787000000000000)
      constant := (413757066584452931225602618208574166156894257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree084.table
  base := (21101692057851087637196965537018997571023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-202397486799834518294188587223173283000000000000)
      constant := (4409753358505655918395225399378315310571754089023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455411555275925505339/100000000000000000000)
  centralHi := (22770577763796275267/5000000000000000000)
  directionLo := (229073392202428265323/50000000000000000000)
  directionHi := (458146784404856530647/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree085.table
  base := (11150750857010891155094524932938474054927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (558)
      previous := (279)
      next := (279)
      square := (3459354683617621023516974790000000000000)
      linear := (-299896503077617417353569612353500000000000)
      constant := (6599972540727875517113103487381446266494343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree085.table
  base := (1115074977074849335482646328583892480983/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (657758)
      previous := (328879)
      next := (328879)
      square := (4077810426499926826499065060790000000000000)
      linear := (-354336133304708073238924095466128500000000000)
      constant := (7815694211255345255920010688845793903307486470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229073392202428265323/50000000000000000000)
  centralHi := (458146784404856530647/100000000000000000000)
  directionLo := (460865780289861432383/100000000000000000000)
  directionHi := (7201027817029084881/1562500000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree086.table
  base := (23526259506662625707871946093487945763933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-175378891805741518553555906416563000000000000)
      constant := (3906858898414270039729353869003110146931989733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree086.table
  base := (23526257645146230266963250972934025072497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-207215083300408014370007667135671263000000000000)
      constant := (4626496529104930095518239797576996379306300874497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460865780289861432383/100000000000000000000)
  centralHi := (7201027817029084881/1562500000000000000)
  directionLo := (7243262946441531999/1562500000000000000)
  directionHi := (463568828572258047937/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree087.table
  base := (12387983856041450986086010465955207739209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (17918)
      previous := (8959)
      next := (8959)
      square := (111083722618388052866267301590000000000000)
      linear := (-9856533601812231659819365382933500000000000)
      constant := (222224328233751284360050844040928055036631401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree087.table
  base := (24775966117268049032693954207810752086147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-209623881550694762407917207091920253000000000000)
      constant := (4736829182732483941052330384638606504706878788147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7243262946441531999/1562500000000000000)
  centralHi := (463568828572258047937/100000000000000000000)
  directionLo := (93251241322682307487/20000000000000000000)
  directionHi := (116564051653352884359/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree088.table
  base := (26050626111240875958836338319767265464999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-179456317859498821199941247369043000000000000)
      constant := (4094321157350743732035855900211618657474462399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree088.table
  base := (26050624745097431858917807769550677759111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-212032679800981510445826747048169243000000000000)
      constant := (4848469214335913357579481908808752701560112085111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93251241322682307487/20000000000000000000)
  centralHi := (116564051653352884359/25000000000000000000)
  directionLo := (117232045956726633819/25000000000000000000)
  directionHi := (468928183826906535277/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree089.table
  base := (6837558629698293852336997500329078647503/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-90747515443188736261566958922641500000000000)
      constant := (2094854322680926884574886756527332867124310606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree089.table
  base := (27350233348684351572909728437027997914583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-214441478051268258483736287004418233000000000000)
      constant := (4961416623363491381838092092206380033134109392583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117232045956726633819/25000000000000000000)
  centralHi := (468928183826906535277/100000000000000000000)
  directionLo := (117896255498444952483/25000000000000000000)
  directionHi := (471585021993779809933/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree090.table
  base := (3584349097241661837626769025810417386903/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (17918)
      previous := (8959)
      next := (8959)
      square := (111083722618388052866267301590000000000000)
      linear := (-10196319106292006880351477128973500000000000)
      constant := (238122242879611083816557999813326842499259868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree090.table
  base := (2867479177585563253603188853743691802851/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-108425138150777503260822913480333611500000000000)
      constant := (2537835704674327452573460858274419130306164844255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117896255498444952483/25000000000000000000)
  centralHi := (471585021993779809933/100000000000000000000)
  directionLo := (237113487780928716109/50000000000000000000)
  directionHi := (474226975561857432219/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree091.table
  base := (7506075189004969368826973957566032312287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-92786228470067387584759629398881500000000000)
      constant := (2191898168209590391396069404182577500088516974) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree091.table
  base := (30024299897949529578814217163414690058601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-219259074551841754559555366916916213000000000000)
      constant := (5191233571896926888154630374964082291134360724601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237113487780928716109/50000000000000000000)
  centralHi := (474226975561857432219/100000000000000000000)
  directionLo := (476854291930165252047/100000000000000000000)
  directionHi := (29803393245635328253/6250000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree092.table
  base := (7849689585218491545574838022061014068643/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-93805584983506713246355964637001500000000000)
      constant := (2241248269414310061422345179761109395185080886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree092.table
  base := (6279751521240908150404032339791408886121/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-221667872802128502597464906873165203000000000000)
      constant := (5308103110674844457123356847894890418181279360605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476854291930165252047/100000000000000000000)
  centralHi := (29803393245635328253/6250000000000000000)
  directionLo := (479467211719312465231/100000000000000000000)
  directionHi := (29966700732457029077/6250000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree093.table
  base := (32798165437642885271121613015376936055229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-21072209221543564201767177750027000000000000)
      constant := (509144553201622857749765980277109934519961181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree093.table
  base := (3279816480870214029772183238322003573117/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-112038335526207625317687223414707096500000000000)
      constant := (2713140012700292660080384233703312672135901475585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479467211719312465231/100000000000000000000)
  centralHi := (29966700732457029077/6250000000000000000)
  directionLo := (482065969028684645421/100000000000000000000)
  directionHi := (241032984514342322711/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree094.table
  base := (17111260983072038583994667670954754248189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-95844298010385364569548635113241500000000000)
      constant := (2341604828084291370626166759717919315799539589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree094.table
  base := (534726897309039024667292487151327512069/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-113242734651350999336641993392831591500000000000)
      constant := (2772882157918016047434670520254339343456594114208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (482065969028684645421/100000000000000000000)
  centralHi := (241032984514342322711/50000000000000000000)
  directionLo := (242325395840612155061/50000000000000000000)
  directionHi := (484650791681224310123/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree095.table
  base := (17835913929307734290314694234850968457511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-96863654523824690231144970351361500000000000)
      constant := (2392611285357151017362403518831002368957986111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree095.table
  base := (35671827397833269299137492003168119753713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-228894267552988746711193526741912173000000000000)
      constant := (5666555981780054063103694017340943143333003811713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242325395840612155061/50000000000000000000)
  centralHi := (484650791681224310123/100000000000000000000)
  directionLo := (121805475364130855987/25000000000000000000)
  directionHi := (487221901456523423949/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree096.table
  base := (37146083057810175204935289756261832057389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-21751780230503114642831401242107000000000000)
      constant := (543148858033651606010037046202151669464585421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree096.table
  base := (742921653269491553038020482846522513147/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-115651532901637747374551533349080581500000000000)
      constant := (2894327511531409836057670372137458585795780378675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121805475364130855987/25000000000000000000)
  centralHi := (487221901456523423949/100000000000000000000)
  directionLo := (489779514312902802653/100000000000000000000)
  directionHi := (244889757156451401327/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree097.table
  base := (19322643757691432869517225348054943393697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-98902367550703341554337640827601500000000000)
      constant := (2496280555404261896316371025602583907767005897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree097.table
  base := (19322643588974311037926195532102596912943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-116855932026781121393506303327205076500000000000)
      constant := (2956030719770490861315005160776885968487680150943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489779514312902802653/100000000000000000000)
  centralHi := (244889757156451401327/50000000000000000000)
  directionLo := (492323840599107794723/100000000000000000000)
  directionHi := (123080960149776948681/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree098.table
  base := (40169441190523163948512884335233965581607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-199843448128285334431867952131443000000000000)
      constant := (5097886736125132261766322163752027544477759807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree098.table
  base := (5021180112726284527580717183538170826589/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-118060331151924495412461073305329571500000000000)
      constant := (3018387615546800708906208003240159634419970802356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492323840599107794723/100000000000000000000)
  centralHi := (123080960149776948681/25000000000000000000)
  directionLo := (247427542628103773359/50000000000000000000)
  directionHi := (494855085256207546719/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree099.table
  base := (5214818006099786613748851916249624758711/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (17918)
      previous := (8959)
      next := (8959)
      square := (111083722618388052866267301590000000000000)
      linear := (-11215675619731332541947812367093500000000000)
      constant := (289128699897951678261853497655063566221069916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree099.table
  base := (65185224690308927962251888505130419477/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-119264730277067869431415843283454066500000000000)
      constant := (3081398198809348982650421507034863139799008472640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247427542628103773359/50000000000000000000)
  centralHi := (494855085256207546719/100000000000000000000)
  directionLo := (248686724005123149871/50000000000000000000)
  directionHi := (497373448010246299743/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree100.table
  base := (10823149015293236747170234120001911599263/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-101960437091021318539126646541961500000000000)
      constant := (2655925348423498401758891323647149944139366126) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree100.table
  base := (8658519169975954797652414000090412070567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-240938258804422486900741226523157123000000000000)
      constant := (6290124939030327797091130362896342692493852462835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248686724005123149871/50000000000000000000)
  centralHi := (497373448010246299743/100000000000000000000)
  directionLo := (499879123556159242457/100000000000000000000)
  directionHi := (249939561778079621229/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree101.table
  base := (44891597203179274248990137302465971939113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-205959587208921288401445963560163000000000000)
      constant := (5420489032113091163295103551895731993013632913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree101.table
  base := (44891597022449571853014983660386692561711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-243347057054709234938650766479406113000000000000)
      constant := (6418760855256112181255150434128515265280898487711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499879123556159242457/100000000000000000000)
  centralHi := (249939561778079621229/50000000000000000000)
  directionLo := (125593075433358052937/25000000000000000000)
  directionHi := (502372301733432211749/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree102.table
  base := (4651554745421400010492890230506476054579/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (62)
      previous := (31)
      next := (31)
      square := (384372742624180113724108310000000000000)
      linear := (-39984294547443279454947834301500000000000)
      constant := (1063097194138374504199762964590532380272895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree102.table
  base := (46515547299641926692814407123766742469823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1315516)
      previous := (657758)
      next := (657758)
      square := (8155620852999853652998130121580000000000000)
      linear := (-850366281332166031060762306005727000000000000)
      constant := (22659875938529911604163477360476762870862352207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125593075433358052937/25000000000000000000)
  centralHi := (502372301733432211749/100000000000000000000)
  directionLo := (504853167693953759949/100000000000000000000)
  directionHi := (10097063353879075199/2000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree103.table
  base := (48164446796943236652629848374119381372683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-210037013262678591047831304512643000000000000)
      constant := (5641078412186110383736013753528258510950348483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree103.table
  base := (48164446664755613695093969548387219938893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-23391898723280491188092171400877000000000000)
      constant := (629649807891056522024588615936994906562340077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504853167693953759949/100000000000000000000)
  centralHi := (10097063353879075199/2000000000000000000)
  directionLo := (507321902062479592673/100000000000000000000)
  directionHi := (253660951031239796337/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree104.table
  base := (24919147608399249166118959855827133768947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-106037863144778621185511987494441500000000000)
      constant := (2876514728455028585510230493475062374933031147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree104.table
  base := (6229786887970545208577325458595941102139/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-125286725902784739526189693174076541500000000000)
      constant := (3406256426128165092711699767275433987060397104556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507321902062479592673/100000000000000000000)
  centralHi := (253660951031239796337/50000000000000000000)
  directionLo := (509778681090102937983/100000000000000000000)
  directionHi := (3982645946016429203/781250000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree105.table
  base := (5153709270154996554031895180632691890337/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (17918)
      previous := (8959)
      next := (8959)
      square := (111083722618388052866267301590000000000000)
      linear := (-11895246628690882983012035859173500000000000)
      constant := (325893596558214153995109798898419239781536965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree105.table
  base := (51537092604902982446624433389282611886853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-252982250055856227090288926304402073000000000000)
      constant := (6946378267219407004712375470530588979827703184853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509778681090102937983/100000000000000000000)
  centralHi := (3982645946016429203/781250000000000000)
  directionLo := (64027959600137483359/12500000000000000000)
  directionHi := (512223676801099866873/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree106.table
  base := (13315209810236293296040108356838570781459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-108076576171657272508704657970681500000000000)
      constant := (2990122127786418262352207345740628245205149718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree106.table
  base := (53260839158317105845248559259581986956929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-255391048306142975128198466260651063000000000000)
      constant := (7081551056775235591187694600837067952091931270929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64027959600137483359/12500000000000000000)
  centralHi := (512223676801099866873/100000000000000000000)
  directionLo := (514657057133495793209/100000000000000000000)
  directionHi := (51465705713349579321/10000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree107.table
  base := (27504767413201554957038047099014841921397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-109095932685096598170300993208801500000000000)
      constant := (3047754004731341609438620965814720603837553597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree107.table
  base := (27504767377883380717458791343902356756457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-128899923278214861583054003108450026500000000000)
      constant := (3609015610449276093636157227907130327717653918457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514657057133495793209/100000000000000000000)
  centralHi := (51465705713349579321/10000000000000000000)
  directionLo := (258539493036839099231/50000000000000000000)
  directionHi := (517078986073678198463/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree108.table
  base := (28391589725377622923367353414796073794687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (17918)
      previous := (8959)
      next := (8959)
      square := (111083722618388052866267301590000000000000)
      linear := (-12235032133170658203544147605213500000000000)
      constant := (345104222205486083789106309913224065326664543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree108.table
  base := (28391589695187772432565778323150660631773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-130104322403358235602008773086574521500000000000)
      constant := (3677909379784136865175598923687723393147676649773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258539493036839099231/50000000000000000000)
  centralHi := (517078986073678198463/100000000000000000000)
  directionLo := (51948962378536092517/10000000000000000000)
  directionHi := (519489623785360925171/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree109.table
  base := (3661360819251644019900262067324638073507/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-111134645711975249493493663685041500000000000)
      constant := (3164674113132746849041031248196092069033533656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree109.table
  base := (3661360816026148345267476575881423399759/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-131308721528501609620963543064699016500000000000)
      constant := (3747456836383423555706031639828039679950675950072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51948962378536092517/10000000000000000000)
  centralHi := (519489623785360925171/100000000000000000000)
  directionLo := (32618070420824190427/6250000000000000000)
  directionHi := (521889126733187046833/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree110.table
  base := (12081063158649738485277666997439425545981/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-224308004450829150310179997846323000000000000)
      constant := (6447924689149995079371775822594479729225482905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree110.table
  base := (483242525993135272730893758795382249159/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-265026241307289967279836626085647023000000000000)
      constant := (7635315960479698590409386221506973063912967894875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32618070420824190427/6250000000000000000)
  centralHi := (521889126733187046833/100000000000000000000)
  directionLo := (524277647801240244567/100000000000000000000)
  directionHi := (65534705975155030571/12500000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree111.table
  base := (15563451875576359048011954403980483048797/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (17918)
      previous := (8959)
      next := (8959)
      square := (111083722618388052866267301590000000000000)
      linear := (-12574817637650433424076259351253500000000000)
      constant := (364866966018974744597478483270911719202204666) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree111.table
  base := (62253807464612632828785594939815506876537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-267435039557576715317746166041896013000000000000)
      constant := (7777025622694767994960190110288123356898969318537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524277647801240244567/100000000000000000000)
  centralHi := (65534705975155030571/12500000000000000000)
  directionLo := (263327668203359352683/50000000000000000000)
  directionHi := (526655336406718705367/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree112.table
  base := (12825449646359450965602085502360777258793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-228385430504586452956565338798803000000000000)
      constant := (6688390323831303138902617998050457908250602965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree112.table
  base := (16031812049897082122971689208489029030731/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-134921918903931731677827852999072501500000000000)
      constant := (3960021329701057343408058681900037320994500553462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263327668203359352683/50000000000000000000)
  centralHi := (526655336406718705367/100000000000000000000)
  directionLo := (2116089354436042857/400000000000000000)
  directionHi := (529022338609010714251/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree113.table
  base := (16506409494732519150067418478081028798457/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-115212071765732552139879004637521500000000000)
      constant := (3405139747806000453617820418821654511809573314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree113.table
  base := (66025637951409378842677783665131991565249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-272252636058150211393565245954393993000000000000)
      constant := (8064367070593584276865881308612064167771044999249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2116089354436042857/400000000000000000)
  centralHi := (529022338609010714251/100000000000000000000)
  directionLo := (26568939860719863101/5000000000000000000)
  directionHi := (531378797214397262021/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree114.table
  base := (33974488370709932297833907855306812643833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (17918)
      previous := (8959)
      next := (8959)
      square := (111083722618388052866267301590000000000000)
      linear := (-12914603142130208644608371097293500000000000)
      constant := (385181827982094329319030996279777668854067737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree114.table
  base := (16987244179476708257624882456991739359263/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-137330717154218479715737392955321491500000000000)
      constant := (4104999428131263379816205076819431486984479434526) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26568939860719863101/5000000000000000000)
  centralHi := (531378797214397262021/100000000000000000000)
  directionLo := (53372485187659405689/10000000000000000000)
  directionHi := (533724851876594056891/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree115.table
  base := (8737158064676512495903478930135707772327/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-117250784792611203463071675113761500000000000)
      constant := (3528685274011785298451191025698266903663290108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree115.table
  base := (2795890579892986753887112827848272611277/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-277070232558723707469384325866891973000000000000)
      constant := (8356938016403558169269419671302201061861197331925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53372485187659405689/10000000000000000000)
  centralHi := (533724851876594056891/100000000000000000000)
  directionLo := (67007579899166655509/12500000000000000000)
  directionHi := (536060639193333244073/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree116.table
  base := (898381266317670952171568798284418064681/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-118270141306050529124668010351881500000000000)
      constant := (3591286214322867672300694501840554855449411240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree116.table
  base := (17967625322063517259712622801818129631661/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-139739515404505227753646932911570481500000000000)
      constant := (4252592275506179535333875604829023006037604515322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67007579899166655509/12500000000000000000)
  centralHi := (536060639193333244073/100000000000000000000)
  directionLo := (134596573199793459891/25000000000000000000)
  directionHi := (107677258559834767913/20000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree117.table
  base := (73868687104235301570527994670920803166409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-26508777293219967730280965686667000000000000)
      constant := (812097616171233202585765419717690112115092201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree117.table
  base := (18467171772394466358458755581443532163147/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-140943914529648601772601702889694976500000000000)
      constant := (4327369230042752112547928996830686618861481730294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134596573199793459891/25000000000000000000)
  centralHi := (107677258559834767913/20000000000000000000)
  directionLo := (270350971727359657789/50000000000000000000)
  directionHi := (540701943454719315579/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree118.table
  base := (18972955478235699736376603326393978864999/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-120308854332929180447860680828121500000000000)
      constant := (3718144449353615618992567064192123478055724798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree118.table
  base := (18972955475105896979127865077789025795891/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-142148313654791975791556472867819471500000000000)
      constant := (4402799871810159319153389564761842852508455203782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270350971727359657789/50000000000000000000)
  centralHi := (540701943454719315579/100000000000000000000)
  directionLo := (543007719132410882243/100000000000000000000)
  directionHi := (135751929783102720561/25000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree119.table
  base := (77939905730815937273234199533450219564659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1116)
      previous := (558)
      next := (558)
      square := (6918709367235242047033949580000000000000)
      linear := (-839641597552723225670982810147000000000000)
      constant := (26175790616409201618837337623839051976081931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree119.table
  base := (77939905720123795107592770697655203166779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1315516)
      previous := (657758)
      next := (657758)
      square := (8155620852999853652998130121580000000000000)
      linear := (-992060296054915915643676421079197000000000000)
      constant := (30995738413891889046242834568463387050396358411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (543007719132410882243/100000000000000000000)
  centralHi := (135751929783102720561/25000000000000000000)
  directionLo := (109060749019811149007/20000000000000000000)
  directionHi := (136325936274763936259/25000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree120.table
  base := (80012938557313639898454433173779428451779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-27188348302179518171345189178747000000000000)
      constant := (854935812649419508052014984753862254822564131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree120.table
  base := (80012938548182566661739514800444782079421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-289114223810157447658932025648136923000000000000)
      constant := (9111244434067295620993327111600955512300286865421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109060749019811149007/20000000000000000000)
  centralHi := (136325936274763936259/25000000000000000000)
  directionLo := (109518028799048186969/20000000000000000000)
  directionHi := (273795071997620467423/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree121.table
  base := (10263865049005573791148329500634489993297/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-123366923873247157432649686542481500000000000)
      constant := (3912572687906881168830962886507990233890261988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree121.table
  base := (2052773009606180225088219781834991282873/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-145761511030222097848420782802192956500000000000)
      constant := (4633013920488428169669641351259337247415598017460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109518028799048186969/20000000000000000000)
  centralHi := (273795071997620467423/50000000000000000000)
  directionLo := (274933517955887583351/50000000000000000000)
  directionHi := (549867035911775166703/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree122.table
  base := (21058462808685601677762337799616523908519/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-124386280386686483094246021780601500000000000)
      constant := (3978486337024263352111058567385623157372115838) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree122.table
  base := (16846770245616874373403719292277011500429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-293931820310730943734751105560634903000000000000)
      constant := (9422118622342722637253317513890428996186634072145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274933517955887583351/50000000000000000000)
  centralHi := (549867035911775166703/100000000000000000000)
  directionLo := (552134538463293545857/100000000000000000000)
  directionHi := (276067269231646772929/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree123.table
  base := (86381731085244683009615703062625622035481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (35836)
      previous := (17918)
      next := (17918)
      square := (222167445236776105732534603180000000000000)
      linear := (-27867919311139068612409412670827000000000000)
      constant := (898878245394294028228129404930824804768254009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree123.table
  base := (86381731079559896225241566672929120499917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-296340618561017691772660645516883893000000000000)
      constant := (9579516778164483183024590581670802540381866021917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (552134538463293545857/100000000000000000000)
  centralHi := (276067269231646772929/50000000000000000000)
  directionLo := (22175710674366110847/4000000000000000000)
  directionHi := (69299095857394096397/12500000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree124.table
  base := (44277279971737651227765273191949671883597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-126424993413565134417438692256841500000000000)
      constant := (4111969989656961503718987784566897096569235797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree124.table
  base := (88554559938621818516797641871275818982599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-298749416811304439810570185473132883000000000000)
      constant := (9738222308441978656321885760387041129276467516599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22175710674366110847/4000000000000000000)
  centralHi := (69299095857394096397/12500000000000000000)
  directionLo := (278320916985868876671/50000000000000000000)
  directionHi := (556641833971737753343/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree125.table
  base := (22688084452357379969915013826074256918123/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-127444349927004460079035027494961500000000000)
      constant := (4179539993172172311095816413991863284488075846) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree125.table
  base := (90752337805286044395392958510491778590147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-301158215061591187848479725429381873000000000000)
      constant := (9898235213175257823895371718113449491149169292147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278320916985868876671/50000000000000000000)
  centralHi := (556641833971737753343/100000000000000000000)
  directionLo := (558881850402294239287/100000000000000000000)
  directionHi := (69860231300286779911/12500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree126.table
  base := (46487532341580693350043978273115236048353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (17918)
      previous := (8959)
      next := (8959)
      square := (111083722618388052866267301590000000000000)
      linear := (-14273745160049309526736818081453500000000000)
      constant := (471962457202225093669587344118456303217974017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree126.table
  base := (92975064679624279998463192350320526403693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (380184124)
      previous := (190092062)
      next := (190092062)
      square := (2356974426516957705716459605136620000000000000)
      linear := (-303567013311877935886389265385630863000000000000)
      constant := (10059555492364540536834132374165077039774249141693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558881850402294239287/100000000000000000000)
  centralHi := (69860231300286779911/12500000000000000000)
  directionLo := (140278231136099021763/25000000000000000000)
  directionHi := (561112924544396087053/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree127.table
  base := (95222740564773157651627295959754766468151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (322524)
      previous := (161262)
      next := (161262)
      square := (1999507007130984951592811428620000000000000)
      linear := (-258966125907766222804455395942403000000000000)
      constant := (8632672709201310163586042399835248147583660751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree127.table
  base := (1190284257021923400381066518329689739527/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-152987905781082341962149402670939926500000000000)
      constant := (5111091573005093290125720423899365833343180861080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140278231136099021763/25000000000000000000)
  centralHi := (561112924544396087053/100000000000000000000)
  directionLo := (281667581322575120697/50000000000000000000)
  directionHi := (112667032529030048279/20000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree128.table
  base := (48747682727203186838914470968921182923963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (161262)
      previous := (80631)
      next := (80631)
      square := (999753503565492475796405714310000000000000)
      linear := (-130502419467322437063824033209321500000000000)
      constant := (4385562712514244101393109626891475996785227763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree128.table
  base := (48747682725914630772125803164756650393647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-154192304906225715981104172649064421500000000000)
      constant := (5193059087056334735284799631205161566863572095647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell077.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281667581322575120697/50000000000000000000)
  centralHi := (112667032529030048279/20000000000000000000)
  directionLo := (452438935091389757/80000000000000000)
  directionHi := (565548668864237196251/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree129.table
  base := (3118529354757323820784612970409379696739/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (17918)
      previous := (8959)
      next := (8959)
      square := (111083722618388052866267301590000000000000)
      linear := (-14613530664529084747268929827493500000000000)
      constant := (495037909840113146024737080232481971717721136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree129.table
  base := (49896469675017400834292044871305240517851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (190092062)
      previous := (95046031)
      next := (95046031)
      square := (1178487213258478852858229802568310000000000000)
      linear := (-155396704031369090000058942627188916500000000000)
      constant := (5275680288336277217332964565027755400982971683851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell077.Kernel129
