import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell234.Parameters
import ForestUnimodality.BinomialMassData.Q467_742.Batch000_049
import ForestUnimodality.BinomialMassData.Q467_742.Batch050_099
import ForestUnimodality.BinomialMassData.Q467_742.Batch100_149
import ForestUnimodality.BinomialMassData.Q467_742.Batch150_199
import ForestUnimodality.BinomialMassData.Q236_371.Batch000_049
import ForestUnimodality.BinomialMassData.Q236_371.Batch050_099
import ForestUnimodality.BinomialMassData.Q236_371.Batch100_149
import ForestUnimodality.BinomialMassData.Q236_371.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree000.table
  base := (25692206254328041589696241/2500000000000000000000000)
  polynomial :=
    { denominator := 265000000000000000000000000000000000000000
      center := (467)
      previous := (0)
      next := (275)
      square := (7705165279446624174153335295000000000000)
      linear := (-18923621761636025065400623565000000000000)
      constant := (2723373862958772408507801546000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree000.table
  base := (25692206254328041589696241/2500000000000000000000000)
  polynomial :=
    { denominator := 132500000000000000000000000000000000000000
      center := (236)
      previous := (0)
      next := (135)
      square := (3852582639723312087076667647500000000000)
      linear := (-9461810880818012532700311782500000000000)
      constant := (1361686931479386204253900773000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree001.table
  base := (11008994775184279825600212249194003567251/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-148665662026959543040305344955320000000000000)
      constant := (7654159510215515980481242735250461724999974455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree001.table
  base := (10907699800691638993569529389571362057817/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-149205023596520806732496078425970000000000000)
      constant := (7585451409726154054725361790887599224999948485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (48111508724453423913/100000000000000000000)
  directionHi := (24055754362226711957/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree002.table
  base := (15624740454649812258727091431463416696333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-99521016311990785945459925557015000000000000)
      constant := (2244172103299304009372758281871876137499970453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree002.table
  base := (1537580445833938416069184650611438370471/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-50030188940776024818825329513832500000000000)
      constant := (1105626595966087515378695209682304943749994555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48111508724453423913/100000000000000000000)
  centralHi := (24055754362226711957/50000000000000000000)
  directionLo := (68039948144353518831/100000000000000000000)
  directionHi := (4252496759022094927/6250000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree003.table
  base := (4718827991085130369007388783500978842191/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-124709201610501800370767178636370000000000000)
      constant := (1463138622744716434392927073120322707636022862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree003.table
  base := (18494592268655237568229099444801768398857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-251036487929687391818106557684690000000000000)
      constant := (2878933112167784763634713871168160204187076337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68039948144353518831/100000000000000000000)
  centralHi := (4252496759022094927/6250000000000000000)
  directionLo := (41665788769773319197/50000000000000000000)
  directionHi := (16666315507909327679/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree004.table
  base := (12042407077811677856832351076923371766837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-299794773818025629592148863431450000000000000)
      constant := (2158621293488718090291504602073429813359211517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree004.table
  base := (11769925006142285341491246871784160402051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-301952220096270684360911797314050000000000000)
      constant := (2129226386423719433388693864976363621898701691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41665788769773319197/50000000000000000000)
  centralHi := (16666315507909327679/20000000000000000000)
  directionLo := (96223017448906847827/100000000000000000000)
  directionHi := (24055754362226711957/25000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree005.table
  base := (7962277581804634372025650941219072995407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-350171144415047658442763369590160000000000000)
      constant := (1801565981856875438425306459868196926160814887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree005.table
  base := (3883510678774211275317950307911281906497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-176433976131426988451858518471705000000000000)
      constant := (893267185222264960433249112464116752892153577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96223017448906847827/100000000000000000000)
  centralHi := (24055754362226711957/25000000000000000000)
  directionLo := (5379030200397602719/5000000000000000000)
  directionHi := (107580604007952054381/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree006.table
  base := (5307823021722214231236190722811327452201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-400547515012069687293377875748870000000000000)
      constant := (1672447876922694902583493288839413921848397841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree006.table
  base := (645400796186986332740025509983436379441/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-100945921107359317361630569143192500000000000)
      constant := (417200690243087040931306606537320333405277362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5379030200397602719/5000000000000000000)
  centralHi := (107580604007952054381/100000000000000000000)
  directionLo := (117848647130372046337/100000000000000000000)
  directionHi := (58924323565186023169/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree007.table
  base := (3433433131610948071849480102696212328743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (49502)
      previous := (0)
      next := (29150)
      square := (816747519621342162460253541270000000000000)
      linear := (-9202528277736565635591681263420000000000000)
      constant := (34334786450409694004621306673246160431439087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree007.table
  base := (3321522262694022636314004227861527204977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (50032)
      previous := (0)
      next := (28620)
      square := (816747519621342162460253541270000000000000)
      linear := (-9279579930531031877333214616370000000000000)
      constant := (34456327598118927756035289277623029918780393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117848647130372046337/100000000000000000000)
  centralHi := (58924323565186023169/50000000000000000000)
  directionLo := (31822771821254533709/25000000000000000000)
  directionHi := (127291087285018134837/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree008.table
  base := (201636032143887830692686580976978915669/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-250650128103056872497303444033145000000000000)
      constant := (893506329129713537565167749714561774657984145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree008.table
  base := (1926173319164993985981628861919653118563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-505615148762603854532132755831490000000000000)
      constant := (1801739806032782069497816713301882974892129883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31822771821254533709/25000000000000000000)
  centralHi := (127291087285018134837/100000000000000000000)
  directionLo := (68039948144353518831/50000000000000000000)
  directionHi := (136079896288707037663/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree009.table
  base := (222151342606793547884788646762467337479/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-275838313401567886922610697112500000000000000)
      constant := (981574331371766033366184308537656783595894078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree009.table
  base := (813677558427496237212261659111906124923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-556530880929187147074937995460850000000000000)
      constant := (1986440198871784212451458572739941870940526643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68039948144353518831/50000000000000000000)
  centralHi := (136079896288707037663/100000000000000000000)
  directionLo := (7216726308668013587/5000000000000000000)
  directionHi := (144334526173360271741/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree010.table
  base := (-4223189410250658324987650882698328059/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-301026498700078901347917950191855000000000000)
      constant := (1099047248677385133644126358890072597138155905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree010.table
  base := (-10570733285077222454333950350336846633/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-303723306547885219808871617545105000000000000)
      constant := (1115054504537731281189241258936946430462936235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7216726308668013587/5000000000000000000)
  centralHi := (144334526173360271741/100000000000000000000)
  directionLo := (152141949236335141853/100000000000000000000)
  directionHi := (76070974618167570927/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree011.table
  base := (-830512212757547888748288436677832342873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-652429367997179831546450406542420000000000000)
      constant := (2484367895395200753367274983111078978494617407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree011.table
  base := (-442432005559780733361319887046033012767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-329181172631176866080274237359785000000000000)
      constant := (1262733707463708535123364204122516970089737353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152141949236335141853/100000000000000000000)
  centralHi := (76070974618167570927/50000000000000000000)
  directionLo := (159567822536922327893/100000000000000000000)
  directionHi := (79783911268461163947/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree012.table
  base := (-755307686327814270172401172290844284779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-351402869297100930198532456350565000000000000)
      constant := (1408618394293079547570258222762685901798733661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree012.table
  base := (-1557375010113502041899130795192644484001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-709278077428937024703353714348930000000000000)
      constant := (2867893082901879452169428280682729220577618359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159567822536922327893/100000000000000000000)
  centralHi := (79783911268461163947/50000000000000000000)
  directionLo := (41665788769773319197/25000000000000000000)
  directionHi := (166663155079093276789/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree013.table
  base := (-1052902951175465133586192955654078518993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-376591054595611944623839709429920000000000000)
      constant := (1596749511976459582614193150374748228567284487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree013.table
  base := (-2146076926865460591031175367027628795789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-760193809595520317246158953978290000000000000)
      constant := (3254242760946648910818432121001550144918806251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41665788769773319197/25000000000000000000)
  centralHi := (166663155079093276789/100000000000000000000)
  directionLo := (173468511645949891193/100000000000000000000)
  directionHi := (86734255822974945597/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree014.table
  base := (-658181641889404394672374962070715077477/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (24751)
      previous := (0)
      next := (14575)
      square := (408373759810671081230126770635000000000000)
      linear := (-8199576324369856307125448214475000000000000)
      constant := (36845549740610384146780740387776722694734214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree014.table
  base := (-666843932628859146988712359310104764559/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (12508)
      previous := (0)
      next := (7155)
      square := (204186879905335540615063385317500000000000)
      linear := (-4138313988582161274433490783712500000000000)
      constant := (18787032219710850911303411222917915716353769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173468511645949891193/100000000000000000000)
  centralHi := (86734255822974945597/50000000000000000000)
  directionLo := (45004195501922520031/25000000000000000000)
  directionHi := (1440134256061520641/800000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree015.table
  base := (-775945515678591574443025727621502663003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-426967425192633973474454215588630000000000000)
      constant := (2033811972959810379836212689144503753923208154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree015.table
  base := (-1566767246043375483133208442525011944701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-431012636964343451165884716618505000000000000)
      constant := (2075125921946596069469707180077114830919409659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45004195501922520031/25000000000000000000)
  centralHi := (1440134256061520641/800000000000000000)
  directionLo := (186335072050720953051/100000000000000000000)
  directionHi := (46583768012680238263/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree016.table
  base := (-220530069360882873871215709860276489437/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-452155610491144987899761468667985000000000000)
      constant := (2281235223987001287522808405374293469739215064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree016.table
  base := (-222122896577316338553297294980147481711/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-228235251523817548718643668216592500000000000)
      constant := (1164231928576617832389727122169910081879264996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186335072050720953051/100000000000000000000)
  centralHi := (46583768012680238263/25000000000000000000)
  directionLo := (96223017448906847827/50000000000000000000)
  directionHi := (38489206979562739131/20000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree017.table
  base := (-3914246367685240924872974277178007832573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-954687591579312004650137443494680000000000000)
      constant := (5094381718542654035577481274408844323916819707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree017.table
  base := (-1968010235684645218790078451538329066993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-481928369130926743708689956247865000000000000)
      constant := (2600637188812842347472568621949432848890016487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96223017448906847827/50000000000000000000)
  centralHi := (38489206979562739131/20000000000000000000)
  directionLo := (4959220806968676703/2500000000000000000)
  directionHi := (198368832278747068121/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree018.table
  base := (-266683687131911930868831379076510076413/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-502531981088167016750375974826695000000000000)
      constant := (2831275511011849353606569376432740612579506136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree018.table
  base := (-857099136517678834693447892815698884399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-1014772470428436779960185152125090000000000000)
      constant := (5782493679553893966341592471139571949262186205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4959220806968676703/2500000000000000000)
  centralHi := (198368832278747068121/100000000000000000000)
  directionLo := (102059922216530278247/50000000000000000000)
  directionHi := (40823968886612111299/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree019.table
  base := (-17934455047462351620007628245756506349/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-527720166386678031175683227906050000000000000)
      constant := (3133168372234461935712728578038072324831013248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree019.table
  base := (-4606997617319032784091522840723746082557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-1065688202595020072502990391754450000000000000)
      constant := (6399951695412690494723864955072062865450771963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102059922216530278247/50000000000000000000)
  centralHi := (40823968886612111299/20000000000000000000)
  directionLo := (8388528182046717123/4000000000000000000)
  directionHi := (52428301137791982019/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree020.table
  base := (-4890815060283863279057065767162662324251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-1105816703370378091201980961970810000000000000)
      constant := (6905226283475438959284809523388663995027768109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree020.table
  base := (-980839869413772260204050078500699089739/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-1116603934761603365045795631383810000000000000)
      constant := (7053142859966689133892007752452626382946171505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8388528182046717123/4000000000000000000)
  centralHi := (52428301137791982019/25000000000000000000)
  directionLo := (5379030200397602719/2500000000000000000)
  directionHi := (215161208015904108761/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree021.table
  base := (-2584353367716320214230263400526796046533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (24751)
      previous := (0)
      next := (14575)
      square := (408373759810671081230126770635000000000000)
      linear := (-11797888509871429796455055797240000000000000)
      constant := (77334784828748219320183443284831479905288803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree021.table
  base := (-5180037992573433579600877594244482502923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (50032)
      previous := (0)
      next := (28620)
      square := (816747519621342162460253541270000000000000)
      linear := (-23826931978126258318134711653330000000000000)
      constant := (157993120509810765625349831515727248649289293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5379030200397602719/2500000000000000000)
  centralHi := (215161208015904108761/100000000000000000000)
  directionLo := (220474630528336108677/100000000000000000000)
  directionHi := (110237315264168054339/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree022.table
  base := (-5427291145100558465698882107582696344271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-1206569444564422148903209974288230000000000000)
      constant := (8286754897129323990859170729577950092478195289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree022.table
  base := (-5436866372124346538393798580353656837967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-1218435399094769950131406110642530000000000000)
      constant := (8465187986192331948506695721472182319165384153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220474630528336108677/100000000000000000000)
  centralHi := (110237315264168054339/50000000000000000000)
  directionLo := (14103936171878672899/6250000000000000000)
  directionHi := (45132595750011753277/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree023.table
  base := (-354280884338383646418651182563301986237/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-628472907580722088876912240223470000000000000)
      constant := (4514399578948879990692151642585442660498824664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree023.table
  base := (-5676571619677403753214391505987903330719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-1269351131261353242674211350271890000000000000)
      constant := (9223458356596691672506865219403318997656506121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14103936171878672899/6250000000000000000)
  centralHi := (45132595750011753277/20000000000000000000)
  directionLo := (14420918135929291269/6250000000000000000)
  directionHi := (46146938034973732061/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree024.table
  base := (-5893865515669387148078877559546162550449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-1307322185758466206604438986605650000000000000)
      constant := (9804728384002243753268665431554626640393649191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree024.table
  base := (-590066878768545140690843585085281545427/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-660133431713968267608508294950625000000000000)
      constant := (5008132741429572243094787152348943814029411465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14420918135929291269/6250000000000000000)
  centralHi := (46146938034973732061/20000000000000000000)
  directionLo := (117848647130372046337/50000000000000000000)
  directionHi := (9427891770429763707/4000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree025.table
  base := (-3052326671482437522890518728121321000667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-678849278177744117727526746382180000000000000)
      constant := (5307185392917374505288642173391684506147193453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree025.table
  base := (-1222075024321684563193486952649633936987/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-1371182595594519827759821829530610000000000000)
      constant := (10843441822097339707939615992520758676395861665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117848647130372046337/50000000000000000000)
  centralHi := (9427891770429763707/4000000000000000000)
  directionLo := (15034846476391694973/6250000000000000000)
  directionHi := (240557543622267119569/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree026.table
  base := (-6301863431059024369481778344257493525027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-1408074926952510264305667998923070000000000000)
      constant := (11457587924110726744880540627505894333721758693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree026.table
  base := (-3153334604413399794920728459040378133017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-711049163880551560151313534579985000000000000)
      constant := (5852426340282820234275336690194543313393407103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15034846476391694973/6250000000000000000)
  centralHi := (240557543622267119569/100000000000000000000)
  directionLo := (61330380453594380329/25000000000000000000)
  directionHi := (245321521814377521317/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree027.table
  base := (-1297261353185318177943292640276313468981/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-1458451297549532293156282505081780000000000000)
      constant := (12334268173909625597166176378096092189079930895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree027.table
  base := (-3245169097675373197250761038946743973393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-736507029963843206422716154394665000000000000)
      constant := (6300194857350030846616914668583351212758214087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61330380453594380329/25000000000000000000)
  centralHi := (245321521814377521317/100000000000000000000)
  directionLo := (124997366309319957591/50000000000000000000)
  directionHi := (249994732618639915183/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree028.table
  base := (-332931878557974950205950544326017592069/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (24751)
      previous := (0)
      next := (14575)
      square := (408373759810671081230126770635000000000000)
      linear := (-15396200695373003285784663380005000000000000)
      constant := (135146137624918668381831238498932165838781790) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree028.table
  base := (-1665503885281253454979101048336383433871/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (12508)
      previous := (0)
      next := (7155)
      square := (204186879905335540615063385317500000000000)
      linear := (-7775152000480967884633865042952500000000000)
      constant := (69030437420614020234873427793423098934256361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124997366309319957591/50000000000000000000)
  centralHi := (249994732618639915183/100000000000000000000)
  directionLo := (31822771821254533709/12500000000000000000)
  directionHi := (254582174570036269673/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree029.table
  base := (-85242298012726471607213516283477488151/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-779602019371788175428755758699600000000000000)
      constant := (7093837595224973502962301107597126252136328360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree029.table
  base := (-6822211247823815756667948414727293362891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-1574845524260852997931042788048050000000000000)
      constant := (14493510542646058812841185163090640614238319869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31822771821254533709/12500000000000000000)
  centralHi := (254582174570036269673/100000000000000000000)
  directionLo := (259088403601071230643/100000000000000000000)
  directionHi := (64772100900267807661/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree030.table
  base := (-871121483303876526619668832756560305851/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-804790204670299189854063011778955000000000000)
      constant := (7582135304211839737444399862234867131769450036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree030.table
  base := (-3485668041969385694375469178698046876109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-812880628213718145236924013838705000000000000)
      constant := (7745483800365619638773791636152222129925481131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259088403601071230643/100000000000000000000)
  centralHi := (64772100900267807661/25000000000000000000)
  directionLo := (131758793019948708241/50000000000000000000)
  directionHi := (263517586039897416483/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree031.table
  base := (-3553872976327466677312803639781380628739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-829978389968810204279370264858310000000000000)
      constant := (8087030175321691229023864715633977238879735301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree031.table
  base := (-3554860507563553709519846293308652184969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-838338494297009791508326633653385000000000000)
      constant := (8261145677125931509772031046755323804608681871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131758793019948708241/50000000000000000000)
  centralHi := (263517586039897416483/100000000000000000000)
  directionLo := (133936771858998729271/50000000000000000000)
  directionHi := (267873543717997458543/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree032.table
  base := (-1808996070703877358409430634464826754887/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-855166575267321218704677517937665000000000000)
      constant := (8608503063852730676653110571304773561261196866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree032.table
  base := (-7237632799826760936567616319338499411053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-1727592720760602875559458506936130000000000000)
      constant := (17587445086309773939958974699243369602563254027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133936771858998729271/50000000000000000000)
  centralHi := (267873543717997458543/100000000000000000000)
  directionLo := (10886391703096563013/4000000000000000000)
  directionHi := (136079896288707037663/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree033.table
  base := (-7353911688822762566910059121014925803993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-1760709521131664466259969542034040000000000000)
      constant := (18293076993520988806469789782296047097412599487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree033.table
  base := (-7355286514782275875280443917189253851067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-1778508452927186168102263746565490000000000000)
      constant := (18686399193526776267180096266233553910685287053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10886391703096563013/4000000000000000000)
  centralHi := (136079896288707037663/50000000000000000000)
  directionLo := (276379575887083616343/100000000000000000000)
  directionHi := (34547446985885452043/12500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree034.table
  base := (-3730854969228988475588567574560986783309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-905542945864343247555292024096375000000000000)
      constant := (9701123964695390539707849770879911218158565931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree034.table
  base := (-3731427810262104743958495175812347844159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-914712092546884730322534493097425000000000000)
      constant := (9909564900310991785191601781497572630382111081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276379575887083616343/100000000000000000000)
  centralHi := (34547446985885452043/12500000000000000000)
  directionLo := (280535892960717897263/100000000000000000000)
  directionHi := (17533493310044868579/6250000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree035.table
  base := (-7559526026028981683146931879904401578009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (49502)
      previous := (0)
      next := (29150)
      square := (816747519621342162460253541270000000000000)
      linear := (-37989025761749153550228541925540000000000000)
      constant := (419275483732067638111101370871561035967372719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree035.table
  base := (-1512096010826415036365867058698433247537/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (50032)
      previous := (0)
      next := (28620)
      square := (816747519621342162460253541270000000000000)
      linear := (-38374284025721484758936208690290000000000000)
      constant := (428277911153384378462590795745980505038342835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280535892960717897263/100000000000000000000)
  centralHi := (17533493310044868579/6250000000000000000)
  directionLo := (284631524099159697041/100000000000000000000)
  directionHi := (142315762049579848521/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree036.table
  base := (-7647478857239995163165058706369781697529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-1911838632922730552811813060510170000000000000)
      constant := (21719812947662554045712622652673096877370410911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree036.table
  base := (-7648272738998495811067648627360828528557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-1931255649426936045730679465453570000000000000)
      constant := (22185847188319645187777013118825268200500885963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284631524099159697041/100000000000000000000)
  centralHi := (142315762049579848521/50000000000000000000)
  directionLo := (288669052346720543481/100000000000000000000)
  directionHi := (144334526173360271741/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree037.table
  base := (-1545132928335175981787441397719005965651/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-1962215003519752581662427566668880000000000000)
      constant := (22928177421381030352422136917167293999409153545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree037.table
  base := (-7726324823538214246795837112569423654659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-1982171381593519338273484705082930000000000000)
      constant := (23419805880274461876183524654549671958749080581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288669052346720543481/100000000000000000000)
  centralHi := (144334526173360271741/50000000000000000000)
  directionLo := (292650882545221180881/100000000000000000000)
  directionHi := (146325441272610590441/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree038.table
  base := (-7794161244539267464690231918031976152931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-2012591374116774610513042072827590000000000000)
      constant := (24169581406582387779193581390782460770334424229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree038.table
  base := (-7794709898735971063034450236633247245413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-2033087113760102630816289944712290000000000000)
      constant := (24687483593243553932537721146715163215894109267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292650882545221180881/100000000000000000000)
  centralHi := (146325441272610590441/50000000000000000000)
  directionLo := (296579258084984765109/100000000000000000000)
  directionHi := (29657925808498476511/10000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree039.table
  base := (-7853031699840389668232415762590790359717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-2062967744713796639363656578986300000000000000)
      constant := (25444016227202424005639186293881173524098192403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree039.table
  base := (-7853487394867551653400546703446515737033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-2084002845926685923359095184341650000000000000)
      constant := (25988872147184331979476757018259038127439040847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (296579258084984765109/100000000000000000000)
  centralHi := (29657925808498476511/10000000000000000000)
  directionLo := (300456275684138704741/100000000000000000000)
  directionHi := (150228137842069352371/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree040.table
  base := (-395116352381245143985299946911311297239/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1056672057655409334107135542572505000000000000)
      constant := (13375737429019107422346306756685502017367268010) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree040.table
  base := (-395135265905288723711943001421421044233/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-533729644523317303975475105992752500000000000)
      constant := (6830991233619790777962721700846370930253628235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300456275684138704741/100000000000000000000)
  centralHi := (150228137842069352371/50000000000000000000)
  directionLo := (152141949236335141853/50000000000000000000)
  directionHi := (304283898472670283707/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree041.table
  base := (-7942088626053867601256517531790851403777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-2163720485907840697064885591303720000000000000)
      constant := (28091951609263933767778049316721477921932729943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree041.table
  base := (-158848049120351755651307932361874782139/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1092917155129926254222352831800185000000000000)
      constant := (14346378308184272502308085182147699827790147525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152141949236335141853/50000000000000000000)
  centralHi := (304283898472670283707/100000000000000000000)
  directionLo := (61612793522601935319/20000000000000000000)
  directionHi := (77015991903252419149/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree042.table
  base := (-62283983778505426983271755913624885803/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (24751)
      previous := (0)
      next := (14575)
      square := (408373759810671081230126770635000000000000)
      linear := (-22592825066376150264443878545535000000000000)
      constant := (300667774198836788449854075901952172529879872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree042.table
  base := (-3986305077783807516306791467653915607417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (25016)
      previous := (0)
      next := (14310)
      square := (408373759810671081230126770635000000000000)
      linear := (-22823980024759548989668478604385000000000000)
      constant := (307094315083927754294984333155240151058765647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61612793522601935319/20000000000000000000)
  centralHi := (77015991903252419149/25000000000000000000)
  directionLo := (155899106326185071611/50000000000000000000)
  directionHi := (311798212652370143223/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree043.table
  base := (-3996569038264868509873452300885962147591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1132236613550942377383057301810570000000000000)
      constant := (15435970954830843920393939785678161534043427169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree043.table
  base := (-1998338439223686945841118991824014046459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-571916443648254773382579035714772500000000000)
      constant := (7882855058051557671914514498340300882631336781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155899106326185071611/50000000000000000000)
  centralHi := (311798212652370143223/100000000000000000000)
  directionLo := (157744130386011344917/50000000000000000000)
  directionHi := (63097652154404537967/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree044.table
  base := (-4002237539505917207101696033017513752729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1157424798849453391808364554889925000000000000)
      constant := (16155724348235746316316694534267246389560627711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree044.table
  base := (-4002326874904665407555816015632061156411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1169290753379801193036560691244225000000000000)
      constant := (16500642929037245819480282505840947470370433549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157744130386011344917/50000000000000000000)
  centralHi := (63097652154404537967/20000000000000000000)
  directionLo := (319135645073844655787/100000000000000000000)
  directionHi := (79783911268461163947/25000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree045.table
  base := (-8006378762676576736964592490113684960061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-2365225968295928812467343615938560000000000000)
      constant := (33783959777558698028232617620930524788412243899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree045.table
  base := (-4003263353431393653160843321008589119297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1194748619463092839307963311058905000000000000)
      constant := (17252418737383576168554329762641156785030841623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319135645073844655787/100000000000000000000)
  centralHi := (79783911268461163947/25000000000000000000)
  directionLo := (322741812023856163141/100000000000000000000)
  directionHi := (161370906011928081571/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree046.table
  base := (-3999431794191272441838308142024501900427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1207801169446475420658979061048635000000000000)
      constant := (17644736581258134047263969472797975533923327293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree046.table
  base := (-7998986036326278148543687832882405508301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-2440412971092768971158731861747170000000000000)
      constant := (36042073236756361925828639013807272823431942059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322741812023856163141/100000000000000000000)
  centralHi := (161370906011928081571/50000000000000000000)
  directionLo := (326308128155253381461/100000000000000000000)
  directionHi := (163154064077626690731/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree047.table
  base := (-7981941287091945705813248948371535360461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-2465978709489972870168572628255980000000000000)
      constant := (36827987236682833718275649732452246001450787499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree047.table
  base := (-997755323745880374698070955923627069979/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-622832175814838065925384275344132500000000000)
      constant := (9403247912598506442913895385963342092922040922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (326308128155253381461/100000000000000000000)
  centralHi := (163154064077626690731/50000000000000000000)
  directionLo := (164917943059517043027/50000000000000000000)
  directionHi := (65967177223806817211/20000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree048.table
  base := (-7955621378477058361606286322895167661731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-2516355080086994899019187134414690000000000000)
      constant := (38399500689761182723857567370311586227871683429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree048.table
  base := (-7955705153720493444534775311220973596207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-2542244435425935556244342341005890000000000000)
      constant := (39217591506375207887780206593548233973244472313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (164917943059517043027/50000000000000000000)
  centralHi := (65967177223806817211/20000000000000000000)
  directionLo := (41665788769773319197/12500000000000000000)
  directionHi := (333326310158186553577/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree049.table
  base := (-7919911590695940414073405645551255735173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (49502)
      previous := (0)
      next := (29150)
      square := (816747519621342162460253541270000000000000)
      linear := (-52382274503755447507546972256600000000000000)
      constant := (816408417511018610413109709111589022639899043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree049.table
  base := (-7919980843895140082949458234560789105571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (50032)
      previous := (0)
      next := (28620)
      square := (816747519621342162460253541270000000000000)
      linear := (-52921636073316711199737705727250000000000000)
      constant := (833793302555185480971326328942998743402451061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41665788769773319197/12500000000000000000)
  centralHi := (333326310158186553577/100000000000000000000)
  directionLo := (67356112214234793479/20000000000000000000)
  directionHi := (84195140267793491849/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree050.table
  base := (-3937409100115897970651197669822077769017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1308553910640519478360208073366055000000000000)
      constant := (20820760838808798292458996787274519393794731103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree050.table
  base := (-1968718856788433059225034992978436773507/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-661018974939775535332488205066152500000000000)
      constant := (10631957953287860082846350886065954984057723013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67356112214234793479/20000000000000000000)
  centralHi := (84195140267793491849/25000000000000000000)
  directionLo := (340199740721767594157/100000000000000000000)
  directionHi := (170099870360883797079/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree051.table
  base := (-3910173153531953816167819620321075770799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1333742095939030492785515326445410000000000000)
      constant := (21656013823263994149640969050528713059831454841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree051.table
  base := (-7820393578977505678031611729536839446611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-2694991631925685433872758059893970000000000000)
      constant := (44233470826679350406306486165298459881729015349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (340199740721767594157/100000000000000000000)
  centralHi := (170099870360883797079/50000000000000000000)
  directionLo := (343584896144899032713/100000000000000000000)
  directionHi := (171792448072449516357/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree052.table
  base := (-775650005751110197358791016977332393309/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1358930281237541507210822579524765000000000000)
      constant := (22507764897033808728458796790053184960262779655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree052.table
  base := (-1939134773118204264703645550555185731231/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-686476841023067181603890824880832500000000000)
      constant := (11493197085925216689088879291462793680767633929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (343584896144899032713/100000000000000000000)
  centralHi := (171792448072449516357/50000000000000000000)
  directionLo := (346937023291899782387/100000000000000000000)
  directionHi := (86734255822974945597/25000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree053.table
  base := (-7683282824725532581082353101352778808199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25970000000000000000000000000000000000000000
      center := (45766)
      previous := (0)
      next := (26950)
      square := (755106197385769169067026858910000000000000)
      linear := (-52230885529662359307023767268080000000000000)
      constant := (882113729357593367584187138005399333435107197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree053.table
  base := (-3841657523542840306809155107531164861963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12985000000000000000000000000000000000000000
      center := (23128)
      previous := (0)
      next := (13230)
      square := (377553098692884584533513429455000000000000)
      linear := (-26385123549611811499607250369365000000000000)
      constant := (450431923965641137134902616905441564853482089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346937023291899782387/100000000000000000000)
  centralHi := (86734255822974945597/25000000000000000000)
  directionLo := (437821338066374131/125000000000000000)
  directionHi := (350257070453099304801/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree054.table
  base := (-1900174338726473967695729385122805825419/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1409306651834563536061437085683475000000000000)
      constant := (24260760427096473300512609164881933766767006842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree054.table
  base := (-3800361972470734134583614975664623200947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1423869414212717655750586889391025000000000000)
      constant := (24776228636127796714386344499128105597998453973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437821338066374131/125000000000000000)
  centralHi := (350257070453099304801/100000000000000000000)
  directionLo := (88386485347779034753/25000000000000000000)
  directionHi := (353545941391116139013/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree055.table
  base := (-7508745885757127469540269638368084032119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-2868989674266149100973488677525660000000000000)
      constant := (50324009080789166769492141086824991045735108721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree055.table
  base := (-7508767821037293621233531175358503250397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-2898654560592018604043979018411410000000000000)
      constant := (51392808059294727721338872013336280254112106523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88386485347779034753/25000000000000000000)
  centralHi := (353545941391116139013/100000000000000000000)
  directionLo := (356804498214181271121/100000000000000000000)
  directionHi := (178402249107090635561/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree056.table
  base := (-1851857560619345698162085547511068313757/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (24751)
      previous := (0)
      next := (14575)
      square := (408373759810671081230126770635000000000000)
      linear := (-29789449437379297243103093711065000000000000)
      constant := (532239715148153159978022595730862818213313174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree056.table
  base := (-3703724166156741138203634389168954822219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (25016)
      previous := (0)
      next := (14310)
      square := (408373759810671081230126770635000000000000)
      linear := (-30097656048557162210069227122865000000000000)
      constant := (543539143606249388338587394815704405904386829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356804498214181271121/100000000000000000000)
  centralHi := (178402249107090635561/50000000000000000000)
  directionLo := (45004195501922520031/12500000000000000000)
  directionHi := (360033564015380160249/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree057.table
  base := (-364837595777282759117314316752155502473/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1484871207730096579337358844921540000000000000)
      constant := (27013984830115728101734149606083716894841138070) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree057.table
  base := (-114011981713466516920073536310448876461/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-750121506231296297282397374417532500000000000)
      constant := (13793635282167657261913046280226706099120503984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45004195501922520031/12500000000000000000)
  centralHi := (360033564015380160249/100000000000000000000)
  directionLo := (363233925300707562837/100000000000000000000)
  directionHi := (181616962650353781419/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree058.table
  base := (-7176712123768765707548148188872261986609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-3020118786057215187525332196001790000000000000)
      constant := (55929441640168716687611997357069032987901150631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree058.table
  base := (-7176724416147158271887554878055618649481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-3051401757091768481672394737299490000000000000)
      constant := (57115923073242360782585145767389946593466785679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363233925300707562837/100000000000000000000)
  centralHi := (181616962650353781419/50000000000000000000)
  directionLo := (366406334226229172689/100000000000000000000)
  directionHi := (36640633422622917269/10000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree059.table
  base := (-352365593269380248793110610264621288257/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1535247578327118608187973351080250000000000000)
      constant := (28931953943465958353077748467914638862630182630) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree059.table
  base := (-7047321994087426975394690175472103454827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-3102317489258351774215199976928850000000000000)
      constant := (59090981782931677762533742196405964208374156893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366406334226229172689/100000000000000000000)
  centralHi := (36640633422622917269/10000000000000000000)
  directionLo := (18477575533118943091/5000000000000000000)
  directionHi := (369551510662378861821/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree060.table
  base := (-107946124367336207054600556279265872351/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1560435763625629622613280604159605000000000000)
      constant := (29915684143889151143614612895532348114039552288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree060.table
  base := (-6908560303130349406695032080872531823261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-3153233221424935066758005216558210000000000000)
      constant := (61099717155932732809414674188850223847314532699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18477575533118943091/5000000000000000000)
  centralHi := (369551510662378861821/100000000000000000000)
  directionLo := (186335072050720953051/50000000000000000000)
  directionHi := (372670144101441906103/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree061.table
  base := (-6760433079702458281733302935452530206773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-3171247897848281274077175714477920000000000000)
      constant := (61831822749997306433820649619887480789809557507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree061.table
  base := (-6760439951051830690049870981073301513571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-3204148953591518359300810456187570000000000000)
      constant := (63142129108590642566019493474590929706370573989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186335072050720953051/50000000000000000000)
  centralHi := (372670144101441906103/100000000000000000000)
  directionLo := (375762895422542529467/100000000000000000000)
  directionHi := (93940723855635632367/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree062.table
  base := (-1650738945309386736107220592541318917071/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1610812134222651651463895110318315000000000000)
      constant := (31932635598580428536231803595059010645870860978) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree062.table
  base := (-1650740359667866611581682476221891732479/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-813766171439525412960903923954232500000000000)
      constant := (16304554392993024267874093329104802600049857961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (375762895422542529467/100000000000000000000)
  centralHi := (93940723855635632367/25000000000000000000)
  directionLo := (189415199263467101109/50000000000000000000)
  directionHi := (378830398526934202219/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree063.table
  base := (-6436120523184131513098055903834830129711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (49502)
      previous := (0)
      next := (29150)
      square := (816747519621342162460253541270000000000000)
      linear := (-66775523245761741464865402587660000000000000)
      constant := (1345545174818003878315162476463140462165641801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree063.table
  base := (-6436125180011816988073433451334268357761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (50032)
      previous := (0)
      next := (28620)
      square := (816747519621342162460253541270000000000000)
      linear := (-67468988120911937640539202764210000000000000)
      constant := (1374040458961033002078896297728602040183049351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (189415199263467101109/50000000000000000000)
  centralHi := (378830398526934202219/100000000000000000000)
  directionLo := (95468315463763601127/25000000000000000000)
  directionHi := (381873261855054404509/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree064.table
  base := (-6259927686332791257876490504817368215327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-3322377009639347360629019232954050000000000000)
      constant := (68031149804348909207437968752423552621474176393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree064.table
  base := (-250397260744485579426471601458198413281/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-3356896150091268236929226175075650000000000000)
      constant := (69471423812661115760940983209245422804939746975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95468315463763601127/25000000000000000000)
  centralHi := (381873261855054404509/100000000000000000000)
  directionLo := (96223017448906847827/25000000000000000000)
  directionHi := (384892069795627391309/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree065.table
  base := (-1518594396934129908273161614159640544041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1686376690118184694739816869556380000000000000)
      constant := (35081789934160761755200702902711137081755305438) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree065.table
  base := (-607438074073256158192651407469788178741/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1703905941128925764736015707352505000000000000)
      constant := (35824270751641231409917077125665954426449550095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96223017448906847827/25000000000000000000)
  centralHi := (384892069795627391309/100000000000000000000)
  directionLo := (387887383996057888217/100000000000000000000)
  directionHi := (193943691998028944109/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree066.table
  base := (-2939735246255190825084903677915856552099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1711564875416695709165124122635735000000000000)
      constant := (36164501860754665141547980164089803588312541541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree066.table
  base := (-5879473086043572442309146547490672896073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-3458727614424434822014836654334370000000000000)
      constant := (73859335527966172479324892572736276291911616207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387887383996057888217/100000000000000000000)
  centralHi := (193943691998028944109/50000000000000000000)
  directionLo := (195429872291218841107/50000000000000000000)
  directionHi := (78171948916487536443/20000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree067.table
  base := (-1418801655852122549483364432161418786783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1736753060715206723590431375715090000000000000)
      constant := (37263710666626115336695401902509066563536802194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree067.table
  base := (-283760437814085004813077962174779951407/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-877410836647754528639410473490932500000000000)
      constant := (19025951464736256821227853272148815563541945565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195429872291218841107/50000000000000000000)
  centralHi := (78171948916487536443/20000000000000000000)
  directionLo := (24613104456041899577/6250000000000000000)
  directionHi := (393809671296670393233/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree068.table
  base := (-5461586168598773212174608102834934618369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-3523882492027435476031477257588890000000000000)
      constant := (76758832677650602912275725755887196764193072471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree068.table
  base := (-5461587922260121590605499530219383969267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-3560559078757601407100447133593090000000000000)
      constant := (78381952472708130734692123669497873771086120853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24613104456041899577/6250000000000000000)
  centralHi := (393809671296670393233/100000000000000000000)
  directionLo := (4959220806968676703/1250000000000000000)
  directionHi := (396737664557494136241/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree069.table
  base := (-5238609287976312479848165251157254771211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-3574258862624457504882091763747600000000000000)
      constant := (79023237732696328047512465857677646796035746749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree069.table
  base := (-5238610729548505811072936390791761607313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-3611474810924184699643252373222450000000000000)
      constant := (80693775349219128033565990372637151140607831367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4959220806968676703/1250000000000000000)
  centralHi := (396737664557494136241/100000000000000000000)
  directionLo := (99911051612883990067/25000000000000000000)
  directionHi := (399644206451535960269/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree070.table
  base := (-2503138059145735444883338324586382747459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (24751)
      previous := (0)
      next := (14575)
      square := (408373759810671081230126770635000000000000)
      linear := (-36986073808382444221762308876595000000000000)
      constant := (829802413056805605925734451666386850862387669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree070.table
  base := (-200251092123048810432455828449347483297/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (50032)
      previous := (0)
      next := (28620)
      square := (816747519621342162460253541270000000000000)
      linear := (-74742664144709550860939951282690000000000000)
      constant := (1694679070842502369572087440561944572985468175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99911051612883990067/25000000000000000000)
  centralHi := (399644206451535960269/100000000000000000000)
  directionLo := (201264880829978044367/50000000000000000000)
  directionHi := (80505952331991217747/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree071.table
  base := (-4764586777316711505579173074207121122513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-3675011603818501562583320776065020000000000000)
      constant := (83651028902052147323360540727550110141576188167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree071.table
  base := (-2382293875432199807381845642458555412077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1856653137628675642364431426240585000000000000)
      constant := (42709224912015228981648601240429381974526309643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201264880829978044367/50000000000000000000)
  centralHi := (80505952331991217747/20000000000000000000)
  directionLo := (81078955665145123451/20000000000000000000)
  directionHi := (50674347290715702157/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree072.table
  base := (-2256770683616810298677538838818859612979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1862693987207761795716967641111865000000000000)
      constant := (43007207493043773079814766889215753344009957461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree072.table
  base := (-2203878011256377238477552960942920157/4882812500000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-941055501855983644317917023027632500000000000)
      constant := (21957825348626281889044249558932422029655225856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81078955665145123451/20000000000000000000)
  centralHi := (50674347290715702157/12500000000000000000)
  directionLo := (102059922216530278247/25000000000000000000)
  directionHi := (408239688866121112989/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree073.table
  base := (-2126569988693646422082737700212947949283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1887882172506272810142274894191220000000000000)
      constant := (44205397359687798856403466106795620881312738597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree073.table
  base := (-4253140634357665753482138347173407711839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-3815137739590517869814473331739890000000000000)
      constant := (90277829171321585902180949267997704989134768201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102059922216530278247/25000000000000000000)
  centralHi := (408239688866121112989/100000000000000000000)
  directionLo := (411064910734607130549/100000000000000000000)
  directionHi := (8221298214692142611/2000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree074.table
  base := (-995845671631848549190472447141218468841/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-1913070357804783824567582147270575000000000000)
      constant := (45420084045538559605882672790317631097460511838) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree074.table
  base := (-3983383226063843747760669164957535011583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-3866053471757101162357278571369250000000000000)
      constant := (92758033144392725791631284758561199923470704297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411064910734607130549/100000000000000000000)
  centralHi := (8221298214692142611/2000000000000000000)
  directionLo := (103467711783976866899/25000000000000000000)
  directionHi := (413870847135907467597/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree075.table
  base := (-3704269564632650557193738299806849232321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-3876517086206589677985778800699860000000000000)
      constant := (93302535091560168844620790011261097964814105239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree075.table
  base := (-3704270007648197196665082294455817526013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-3916969203923684454900083810998610000000000000)
      constant := (95271913304706282162010979496015806819902044667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103467711783976866899/25000000000000000000)
  centralHi := (413870847135907467597/100000000000000000000)
  directionLo := (41665788769773319197/10000000000000000000)
  directionHi := (416657887697733191971/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree076.table
  base := (-3415800674397217633059845939802437287827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-3926893456803611706836393306858570000000000000)
      constant := (95797895712195460325623655632865992729266203893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree076.table
  base := (-3415801038096330427351329349429089495039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-3967884936090267747442889050627970000000000000)
      constant := (97819469644143417448125961144291870692813337001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41665788769773319197/10000000000000000000)
  centralHi := (416657887697733191971/100000000000000000000)
  directionLo := (8388528182046717123/2000000000000000000)
  directionHi := (419426409102335856151/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree077.table
  base := (-15589880362212791925894446105988852993/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (24751)
      previous := (0)
      next := (14575)
      square := (408373759810671081230126770635000000000000)
      linear := (-40584385993884017711091916459360000000000000)
      constant := (1003329081073362845626366316240538981194266300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree077.table
  base := (-779494092743910932227296332437820274961/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (12508)
      previous := (0)
      next := (7155)
      square := (204186879905335540615063385317500000000000)
      linear := (-20504085042126791020335174950292500000000000)
      constant := (512248480384342148504008285625672162847634551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8388528182046717123/2000000000000000000)
  centralHi := (419426409102335856151/100000000000000000000)
  directionLo := (105544193920196043703/25000000000000000000)
  directionHi := (422176775680784174813/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree078.table
  base := (-2810795810306432708226445395160739655323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-4027646197997655764537622319175990000000000000)
      constant := (100887597783448755672238478958953580633101686957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree078.table
  base := (-1405398027654727288813428569557689980767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-2034858200211717166264249764943345000000000000)
      constant := (51507805415760797348618091462302109993357249353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105544193920196043703/25000000000000000000)
  centralHi := (422176775680784174813/100000000000000000000)
  directionLo := (424909339972618533373/100000000000000000000)
  directionHi := (212454669986309266687/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree079.table
  base := (-498851987050171467376244722223989133073/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-4078022568594677793388236825334700000000000000)
      constant := (103481939220467859482809483328971772058673496035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree079.table
  base := (-2494260136290120771927577926639864437017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-4120632132590017625071304769516050000000000000)
      constant := (105664195666494696899744865736331482419024543103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424909339972618533373/100000000000000000000)
  centralHi := (212454669986309266687/50000000000000000000)
  directionLo := (5345305540666464619/1250000000000000000)
  directionHi := (427624443253317169521/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree080.table
  base := (-433673698184598278127953640726537620333/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-4128398939191699822238851331493410000000000000)
      constant := (106109274250239231674730288242874593176998727735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree080.table
  base := (-433673731172330750695437997602183898169/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-4171547864756600917614110009145410000000000000)
      constant := (108346456654477152035469344218392989030360603355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5345305540666464619/1250000000000000000)
  centralHi := (427624443253317169521/100000000000000000000)
  directionLo := (430322416031808217521/100000000000000000000)
  directionHi := (215161208015904108761/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree081.table
  base := (-1833121517896495166157246100321901055241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-4178775309788721851089465837652120000000000000)
      constant := (108769602867178273071108979869577095716855573519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree081.table
  base := (-1833121653196497349360818383964390752153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-4222463596923184210156915248774770000000000000)
      constant := (111062393790077225763605794672303997292482908927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430322416031808217521/100000000000000000000)
  centralHi := (215161208015904108761/50000000000000000000)
  directionLo := (216501789260040407611/50000000000000000000)
  directionHi := (433003578520080815223/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree082.table
  base := (-744259527057856850462037430208479860521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-2114575840192871939970040171905415000000000000)
      constant := (55731462533031143038320169822904694623518029039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree082.table
  base := (-18606489563580561463542771196254041073/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-1068344832272441875674930122101032500000000000)
      constant := (28453001767057714713658469273497387950653424140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216501789260040407611/50000000000000000000)
  centralHi := (433003578520080815223/100000000000000000000)
  directionLo := (108917060269196048327/25000000000000000000)
  directionHi := (435668241076784193309/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree083.table
  base := (-1134561135260822869049709756517107322497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-4279528050982765908790694849969540000000000000)
      constant := (114189240841980215603836068038395641331024190423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree083.table
  base := (-567280613131931956573722016882324240819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-2162147530628175397621262864016745000000000000)
      constant := (58297648242078726759736569286815000009169432021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108917060269196048327/25000000000000000000)
  centralHi := (435668241076784193309/100000000000000000000)
  directionLo := (438316704626554368561/100000000000000000000)
  directionHi := (219158352313277184281/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree084.table
  base := (-385623897524329202485267538920434818241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (24751)
      previous := (0)
      next := (14575)
      square := (408373759810671081230126770635000000000000)
      linear := (-44182698179385591200421524042125000000000000)
      constant := (1193352552962155537401761292626362498595561031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree084.table
  base := (-771247869666319431466243562854273816027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (50032)
      previous := (0)
      next := (28620)
      square := (816747519621342162460253541270000000000000)
      linear := (-89290016192304777301741448319650000000000000)
      constant := (2436984939455580619612903073062822344850780157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438316704626554368561/100000000000000000000)
  centralHi := (219158352313277184281/50000000000000000000)
  directionLo := (88189852211334443471/20000000000000000000)
  directionHi := (110237315264168054339/25000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree085.table
  base := (-199289532740588292381238654377926666229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-2190140396088404983245961931143480000000000000)
      constant := (59870426553295292998727294482769099045733574211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree085.table
  base := (-99644781663799588593899893386478316263/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-1106531631397379345082034051823052500000000000)
      constant := (30565725927853059181859908529000041738071244417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88189852211334443471/20000000000000000000)
  centralHi := (110237315264168054339/25000000000000000000)
  directionLo := (443566193592532955167/100000000000000000000)
  directionHi := (13861443549766654849/3125000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree086.table
  base := (-16554977051247171623760593780175313059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-4430657162773831995342538368445670000000000000)
      constant := (122566149586681176513005648133384042889735246181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree086.table
  base := (-16555027196921098039325323227382018101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-4477042257756100672870941446921570000000000000)
      constant := (125147221514299204546194085760835499911646560259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443566193592532955167/100000000000000000000)
  centralHi := (13861443549766654849/3125000000000000000)
  directionLo := (89233555430658837237/20000000000000000000)
  directionHi := (223083888576647093093/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree087.table
  base := (374824441086344372351075799684616239777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-4481033533370854024193152874604380000000000000)
      constant := (125424439626550120386237629701616642763859146057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree087.table
  base := (37482439998630231927663106823327131989/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-2263978994961341982706873343275465000000000000)
      constant := (64032607719015500054085731074708767848870489745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89233555430658837237/20000000000000000000)
  centralHi := (223083888576647093093/50000000000000000000)
  directionLo := (17950171147558665637/4000000000000000000)
  directionHi := (224377139344483320463/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree088.table
  base := (38777958048614388462368599503892355707/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-2265704951983938026521883690381545000000000000)
      constant := (64157861611174535095594040984739052477318671870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree088.table
  base := (775559127290534461124934916088316856823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-4578873722089267257956551926180290000000000000)
      constant := (131016885478808189860681715688402912020489974543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17950171147558665637/4000000000000000000)
  centralHi := (224377139344483320463/50000000000000000000)
  directionLo := (14103936171878672899/3125000000000000000)
  directionHi := (451325957500117532769/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree089.table
  base := (37051536116354202172065303664191832763/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-2290893137282449040947190943460900000000000000)
      constant := (65620000185188894357123574675901879698853313328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree089.table
  base := (118564912812442124582662498048324283807/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-2314894727127925275249678582904825000000000000)
      constant := (67001115816485356618284236236888407013737396435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14103936171878672899/3125000000000000000)
  centralHi := (451325957500117532769/100000000000000000000)
  directionLo := (14183845798164696343/3125000000000000000)
  directionHi := (453883065541270282977/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree090.table
  base := (1605094399431856237432470144881016591301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-4632162645161920110744996393080510000000000000)
      constant := (134197271067070324097425569547601968004643260941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree090.table
  base := (321018875364009182581930678086872781343/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-4680705186422433843042162405439010000000000000)
      constant := (137021253896985612505003599364529176282484159315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14183845798164696343/3125000000000000000)
  centralHi := (453883065541270282977/100000000000000000000)
  directionLo := (456425847709005425559/100000000000000000000)
  directionHi := (11410646192725135639/2500000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree091.table
  base := (508473716770235591198081468924546436191/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (24751)
      previous := (0)
      next := (14575)
      square := (408373759810671081230126770635000000000000)
      linear := (-47781010364887164689751131624890000000000000)
      constant := (1399872809275340038101339599687004351878521038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree091.table
  base := (2033894848557320422371072825385999900369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (50032)
      previous := (0)
      next := (28620)
      square := (816747519621342162460253541270000000000000)
      linear := (-96563692216102390522142196838130000000000000)
      constant := (2858652087090543386287205116092069273720136521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (456425847709005425559/100000000000000000000)
  centralHi := (11410646192725135639/2500000000000000000)
  directionLo := (229477271057847563033/50000000000000000000)
  directionHi := (458954542115695126067/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree092.table
  base := (494410106894448677786910757328649651063/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-4732915386355964168446225405397930000000000000)
      constant := (140210793092786102605375522532015703333109811915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree092.table
  base := (309006314912434370128152205999686886553/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-1195634162688900107031943221174432500000000000)
      constant := (35790081685253827117980034560433565805504082946) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229477271057847563033/50000000000000000000)
  centralHi := (458954542115695126067/100000000000000000000)
  directionLo := (14420918135929291269/3125000000000000000)
  directionHi := (461469380349737320609/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree093.table
  base := (729890344541072423599282761422879895503/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-2391645878476493098648419955778320000000000000)
      constant := (71633522207626076696208243275523544473393856846) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree093.table
  base := (583912273147532978091509397112001655419/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-4833452382922183720670578124327090000000000000)
      constant := (146280377314513407451668846203937265099267632895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14420918135929291269/3125000000000000000)
  centralHi := (461469380349737320609/100000000000000000000)
  directionLo := (9279411754461889101/2000000000000000000)
  directionHi := (463970587723094455051/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree094.table
  base := (1688213687709717951434441808661393007813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-2416834063775004113073727208857675000000000000)
      constant := (73178144636625921923769022260498772794988389133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree094.table
  base := (675285473048617184698934766211976127893/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-4884368115088767013213383363956450000000000000)
      constant := (149434103984816271616428342414088033031096602065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9279411754461889101/2000000000000000000)
  centralHi := (463970587723094455051/100000000000000000000)
  directionLo := (466458383506885686867/100000000000000000000)
  directionHi := (116614595876721421717/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree095.table
  base := (768529700831585000730646030801253928459/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-4884044498147030254998068923874060000000000000)
      constant := (149478527663746094136030908288611589459835126095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree095.table
  base := (3842648495825289197978926213175027050403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-4935283847255350305756188603585810000000000000)
      constant := (152621506748897113594362382744381823898244519323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466458383506885686867/100000000000000000000)
  centralHi := (116614595876721421717/25000000000000000000)
  directionLo := (234466490577864880377/50000000000000000000)
  directionHi := (93786596231145952151/20000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree096.table
  base := (4318224742917844746733654893585600825701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-4934420868744052283848683430032770000000000000)
      constant := (152633759583780865193890554607870255683250311341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree096.table
  base := (4318224736095631687205444796477741445643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-4986199579421933598298993843215170000000000000)
      constant := (155842585603811979170632283651031032810319748163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234466490577864880377/50000000000000000000)
  centralHi := (93786596231145952151/20000000000000000000)
  directionLo := (471394588521488185349/100000000000000000000)
  directionHi := (9427891770429763707/2000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree097.table
  base := (2401578035409987539678846061468054303647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-2492398619670537156349648968095740000000000000)
      constant := (77910992515241160146918040672776675712408276727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree097.table
  base := (4803156065234994934297095406427256625911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-5037115311588516890841799082844530000000000000)
      constant := (159097340546695304061715019509117694029247015951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471394588521488185349/100000000000000000000)
  centralHi := (9427891770429763707/2000000000000000000)
  directionLo := (236921704028507231419/50000000000000000000)
  directionHi := (473843408057014462839/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree098.table
  base := (132436061688417730547879265078566643217/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (24751)
      previous := (0)
      next := (14575)
      square := (408373759810671081230126770635000000000000)
      linear := (-51379322550388738179080739207655000000000000)
      constant := (1622889836745434156235869029818013874015931060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree098.table
  base := (331090153935316577024160591700626421367/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (12508)
      previous := (0)
      next := (7155)
      square := (204186879905335540615063385317500000000000)
      linear := (-25959342059975000935635736339152500000000000)
      constant := (828498834565081433115732995402848238470479612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236921704028507231419/50000000000000000000)
  centralHi := (473843408057014462839/100000000000000000000)
  directionLo := (23813981850523731591/5000000000000000000)
  directionHi := (476279637010474631821/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree099.table
  base := (725135489158047544104117585348905678279/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-2542774990267559185200263474254450000000000000)
      constant := (81148708246382874870369827723268001155855999356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree099.table
  base := (1450270977380649555308417965821236219293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-1284736693980420868981852390525812500000000000)
      constant := (41426969671318429235137601431163630774459707813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23813981850523731591/5000000000000000000)
  centralHi := (476279637010474631821/100000000000000000000)
  directionLo := (186993542035455853/39062500000000000)
  directionHi := (478703467610766983681/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree100.table
  base := (6314080388698447296533905575165031057833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-5135926351132140399251141454667610000000000000)
      constant := (165584622502964831230761945739844790039831191953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree100.table
  base := (6314080385636196200749608909139301383717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-5189862508088266768470214801732610000000000000)
      constant := (169063661875596037760477313734538842581756191597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186993542035455853/39062500000000000)
  centralHi := (478703467610766983681/100000000000000000000)
  directionLo := (15034846476391694973/3125000000000000000)
  directionHi := (481115087244534239137/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree101.table
  base := (427276992188193209288062497094829710251/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-2593151360864581214050877980413160000000000000)
      constant := (84452411014529155993444233820726486899189263128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree101.table
  base := (1709107968126302984795100092787079035293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-1310194560063712515253255010340492500000000000)
      constant := (43113280285783795866209635383818716345496763813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15034846476391694973/3125000000000000000)
  centralHi := (481115087244534239137/100000000000000000000)
  directionLo := (483514678625229484829/100000000000000000000)
  directionHi := (48351467862522948483/10000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree102.table
  base := (3684069176915428349707784014074305699541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-2618339546163092228476185233492515000000000000)
      constant := (86129007534258763230012098182905271510790522781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree102.table
  base := (7368138351780462154400749461872894816211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-5291693972421433353555825280991330000000000000)
      constant := (175876256485365554117499081151742687115398098251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483514678625229484829/100000000000000000000)
  centralHi := (48351467862522948483/10000000000000000000)
  directionLo := (242951209977333776389/50000000000000000000)
  directionHi := (485902419954667552779/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree103.table
  base := (1977299951806008074068166803863593247603/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-2643527731461603242901492486571870000000000000)
      constant := (87822100809437030363583537147383783926386649046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree103.table
  base := (7909199805546490226604403249763364851813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-5342609704588016646098630520620690000000000000)
      constant := (179333067899821248353852180124190879301568393133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242951209977333776389/50000000000000000000)
  centralHi := (485902419954667552779/100000000000000000000)
  directionLo := (244139242538733040481/50000000000000000000)
  directionHi := (488278485077466080963/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree104.table
  base := (8459616217677526226227726374057891327923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-5337431833520228514653599479302450000000000000)
      constant := (179063381677717395304326396583853822220266649643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree104.table
  base := (4229808108152581766287691039103922013233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-2696762718377299969320717880125025000000000000)
      constant := (91411777692046902850752883898351862929823403353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244139242538733040481/50000000000000000000)
  centralHi := (488278485077466080963/100000000000000000000)
  directionLo := (490643043628755042633/100000000000000000000)
  directionHi := (245321521814377521317/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree105.table
  base := (901938756808302708667296971810110895237/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (24751)
      previous := (0)
      next := (14575)
      square := (408373759810671081230126770635000000000000)
      linear := (-54977634735890311668410346790420000000000000)
      constant := (1862403624925435970425875779246204257523603665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree105.table
  base := (1803877513392085615442829343181862606817/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (50032)
      previous := (0)
      next := (28620)
      square := (816747519621342162460253541270000000000000)
      linear := (-111111044263697616962943693875090000000000000)
      constant := (3803014672159798126377966295713189260312744765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (490643043628755042633/100000000000000000000)
  centralHi := (245321521814377521317/50000000000000000000)
  directionLo := (123249065293877478091/25000000000000000000)
  directionHi := (98599252235101982473/20000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree106.table
  base := (2397128460430570547576382888648677323667/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12985000000000000000000000000000000000000000
      center := (22883)
      previous := (0)
      next := (13475)
      square := (377553098692884584533513429455000000000000)
      linear := (-51303628063342194078819136713395000000000000)
      constant := (1754723795391499368879833112308881230019126398) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree106.table
  base := (191770276816081469141516580397482513679/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12985000000000000000000000000000000000000000
      center := (23128)
      previous := (0)
      next := (13230)
      square := (377553098692884584533513429455000000000000)
      linear := (-51842989632903457771009870184045000000000000)
      constant := (1791561873138966236214673274602346552200609075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123249065293877478091/25000000000000000000)
  centralHi := (98599252235101982473/20000000000000000000)
  directionLo := (19813531974073668023/4000000000000000000)
  directionHi := (15479321854745053143/3125000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree107.table
  base := (10166995022253351325599773756432593713071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-5488560945311294601205442997778580000000000000)
      constant := (189518882881886698310251246842240991131260805511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree107.table
  base := (10166995021502385934768565206725208549999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-5546272633254349816269851479138130000000000000)
      constant := (193497074232546555547682470127403304430030412359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19813531974073668023/4000000000000000000)
  centralHi := (15479321854745053143/3125000000000000000)
  directionLo := (24883465799427835029/5000000000000000000)
  directionHi := (497669315988556700581/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree108.table
  base := (10754831093697718382583741715172493234183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-5538937315908316630056057503937290000000000000)
      constant := (193070036951656721792809987374366157141246182303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree108.table
  base := (2150966218616717518760280615549240336227/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-5597188365420933108812656718767490000000000000)
      constant := (197122265973080140235097926397026464945593102535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24883465799427835029/5000000000000000000)
  centralHi := (497669315988556700581/100000000000000000000)
  directionLo := (99997893047455966073/20000000000000000000)
  directionHi := (249994732618639915183/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree109.table
  base := (2838005510107040611302812597356579530849/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-2794656843252669329453336005048000000000000000)
      constant := (98327092259329028617416509272917605176411174418) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree109.table
  base := (567601101996298802022099279412025441947/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-1412026024396879100338865489599212500000000000)
      constant := (50195283443045247090456505140182282969275135135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99997893047455966073/20000000000000000000)
  centralHi := (249994732618639915183/50000000000000000000)
  directionLo := (100459779537883560669/20000000000000000000)
  directionHi := (251149448844708901673/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree110.table
  base := (11958567847157305748676361049671581964111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-5639690057102360687757286516254710000000000000)
      constant := (200271325580786534673394686143977946213122202151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree110.table
  base := (298964196168667315459616017521247535861/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-1424754957438524923474566799506552500000000000)
      constant := (51118419406936387994888545903404320320834439010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100459779537883560669/20000000000000000000)
  centralHi := (251149448844708901673/50000000000000000000)
  directionLo := (25229888024511096301/5000000000000000000)
  directionHi := (504597760490221926021/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree111.table
  base := (6287234249463384427112343508211981977967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-2845033213849691358303950511206710000000000000)
      constant := (101960730067991633902082698815921731661429355847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree111.table
  base := (12574468498591058167244857189313576486889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-5749935561920682986441072437655570000000000000)
      constant := (208199897537715454093967931045997149981231888849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25229888024511096301/5000000000000000000)
  centralHi := (504597760490221926021/100000000000000000000)
  directionLo := (506886197448195002349/100000000000000000000)
  directionHi := (10137723948963900047/2000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree112.table
  base := (1319972398109687403440128170111235453707/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (24751)
      previous := (0)
      next := (14575)
      square := (408373759810671081230126770635000000000000)
      linear := (-58575946921391885157739954373185000000000000)
      constant := (2118414165124828946378168639857492301947314815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree112.table
  base := (206245687200350381932690449052761573411/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (12508)
      previous := (0)
      next := (7155)
      square := (204186879905335540615063385317500000000000)
      linear := (-29596180071873807545836110598392500000000000)
      constant := (1081427517857531080633709269881267316155383984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506886197448195002349/100000000000000000000)
  centralHi := (10137723948963900047/2000000000000000000)
  directionLo := (101832869828014507869/20000000000000000000)
  directionHi := (254582174570036269673/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree113.table
  base := (13834334279336846617813103459269044739197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-5790819168893426774309130034730840000000000000)
      constant := (211320709717563939339534863721564113086947814277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree113.table
  base := (2766866855822499360866166218040952408311/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-5851767026253849571526682916914290000000000000)
      constant := (215753365512855304307259799271545473652161671755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101832869828014507869/20000000000000000000)
  centralHi := (254582174570036269673/50000000000000000000)
  directionLo := (255716176505797558803/50000000000000000000)
  directionHi := (511432353011595117607/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree114.table
  base := (14478299379615471263254078395084578867829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-5841195539490448803159744540889550000000000000)
      constant := (215069824740044105076809463461339956519946851389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree114.table
  base := (1447829937943208992198707195985380332443/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-2951341379210216432034744078271825000000000000)
      constant := (109790306787061050252754380619124678671688934815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255716176505797558803/50000000000000000000)
  centralHi := (511432353011595117607/100000000000000000000)
  directionLo := (513690343474276342647/100000000000000000000)
  directionHi := (64211292934284542831/12500000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree115.table
  base := (15131619268192166101858726630342975849353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-5891571910087470832010359047048260000000000000)
      constant := (218851933247782466527871812409444250038880796273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree115.table
  base := (15131619268042283414834466512912935070929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-5953598490587016156612293396173010000000000000)
      constant := (223441537681985441658678929103249249296097738489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513690343474276342647/100000000000000000000)
  centralHi := (64211292934284542831/12500000000000000000)
  directionLo := (806153831247436191/156250000000000000)
  directionHi := (515938451998359162241/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree116.table
  base := (3158858786321688526616961736428026748957/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-5941948280684492860860973553206970000000000000)
      constant := (222667035238926583877018776181210590148765952185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree116.table
  base := (7897146965742974253878518978427695285941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3002257111376799724577549317901185000000000000)
      constant := (113668068917296537552517282352422486406852205181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (806153831247436191/156250000000000000)
  centralHi := (515938451998359162241/100000000000000000000)
  directionLo := (259088403601071230643/50000000000000000000)
  directionHi := (518176807202142461287/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree117.table
  base := (16466323356679723372937240978545466544909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-5992324651281514889711588059365680000000000000)
      constant := (226515130711661718694775787478714879060707819669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree117.table
  base := (16466323356579620377281916143232138038567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-6055429954920182741697903875431730000000000000)
      constant := (231264414030130415562808038722933854711766400447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259088403601071230643/50000000000000000000)
  centralHi := (518176807202142461287/100000000000000000000)
  directionLo := (520405534937849673581/100000000000000000000)
  directionHi := (260202767468924836791/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree118.table
  base := (17147707530487492683075683776119872471481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-6042701021878536918562202565524390000000000000)
      constant := (230396219664209753570166043599330415366847116321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree118.table
  base := (8573853765202846892453325442797252541701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3053172843543383017120354557530545000000000000)
      constant := (117613183133409735464683317705701456637092267341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (520405534937849673581/100000000000000000000)
  centralHi := (260202767468924836791/50000000000000000000)
  directionLo := (522624758374201628473/100000000000000000000)
  directionHi := (261312379187100814237/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree119.table
  base := (8919223220185879540528411118081330206499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (24751)
      previous := (0)
      next := (14575)
      square := (408373759810671081230126770635000000000000)
      linear := (-62174259106893458647069561955950000000000000)
      constant := (2390921449947226067505658818830036706550055691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree119.table
  base := (4459611610076230520980775720934321285381/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (12508)
      previous := (0)
      next := (7155)
      square := (204186879905335540615063385317500000000000)
      linear := (-31414599077823210850936297728012500000000000)
      constant := (1220520380321009233862299998820574508490635229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (522624758374201628473/100000000000000000000)
  centralHi := (261312379187100814237/50000000000000000000)
  directionLo := (52483459807584693293/10000000000000000000)
  directionHi := (524834598075846932931/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree120.table
  base := (1853854007392380974561131605173139690669/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3071726881536290488131715788920905000000000000)
      constant := (119128689000904487094754508073783280600816859145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree120.table
  base := (370770801477384035546295269829590690711/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3104088575709966309663159797159905000000000000)
      constant := (121625649428358784256153841264326967306503818775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52483459807584693293/10000000000000000000)
  centralHi := (524834598075846932931/100000000000000000000)
  directionLo := (105407034415958966593/20000000000000000000)
  directionHi := (263517586039897416483/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree121.table
  base := (9623994209489619984251308796629558834511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3096915066834801502557023042000260000000000000)
      constant := (121118723691738945731791506326859040357540928551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree121.table
  base := (9623994209467313289200109676817324687853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3129546441793257955934562416974585000000000000)
      constant := (123657139603272247365026083637622833387360774773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105407034415958966593/20000000000000000000)
  centralHi := (263517586039897416483/50000000000000000000)
  directionLo := (529226595968987663049/100000000000000000000)
  directionHi := (10584531919379753261/2000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree122.table
  base := (19966791463611242032902092273786425282087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-6244206504266625033964660590159230000000000000)
      constant := (246250510238193288696824543670614477362251736767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree122.table
  base := (19966791463574796438049881367619248943017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-6310008615753099204411930073578530000000000000)
      constant := (251410935590757026861082008234939121043765802897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (529226595968987663049/100000000000000000000)
  centralHi := (10584531919379753261/2000000000000000000)
  directionLo := (531408982943142641499/100000000000000000000)
  directionHi := (1062817965886285283/200000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree123.table
  base := (10347474598062069735862204811360120223461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3147291437431823531407637548158970000000000000)
      constant := (125148283282172680642313758613476424557677395501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree123.table
  base := (161679290594487252331484192785236154583/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-1590231086979920624238683828301972500000000000)
      constant := (63885317001936351547893476769483636065694678496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531408982943142641499/100000000000000000000)
  centralHi := (1062817965886285283/200000000000000000)
  directionLo := (266791221943492935087/50000000000000000000)
  directionHi := (21343297755479434807/4000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree124.table
  base := (21432461605047153922353477914054133141523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-6344959245460669091665889602476650000000000000)
      constant := (254375616360355259822383091841473944939732367243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree124.table
  base := (10716230802511418225361673626454958243941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3205920040043132894748770276418625000000000000)
      constant := (129852638227965410422630280678091446907654283181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266791221943492935087/50000000000000000000)
  centralHi := (21343297755479434807/4000000000000000000)
  directionLo := (107149417487198983417/20000000000000000000)
  directionHi := (267873543717997458543/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree125.table
  base := (2217932867912839288285379668064774779401/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3197667808028845560258252054317680000000000000)
      constant := (129243829812337131287116181647190049577057665205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree125.table
  base := (22179328679108531343625952634933971471313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-6462755812252849082040345792466610000000000000)
      constant := (263902960933764579773430931636469946767282992633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107149417487198983417/20000000000000000000)
  centralHi := (267873543717997458543/50000000000000000000)
  directionLo := (268951510019880135951/50000000000000000000)
  directionHi := (537903020039760271903/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree126.table
  base := (5733887601832261904665177210572030340131/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (24751)
      previous := (0)
      next := (14575)
      square := (408373759810671081230126770635000000000000)
      linear := (-65772571292395032136399169538715000000000000)
      constant := (2679925473018193641501439975719323666450855958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree126.table
  base := (22935550407312826535481583033578602928299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (50032)
      previous := (0)
      next := (28620)
      square := (816747519621342162460253541270000000000000)
      linear := (-132932072335090456624145939430530000000000000)
      constant := (5472129008974026844776102358106682295625591891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268951510019880135951/50000000000000000000)
  centralHi := (537903020039760271903/100000000000000000000)
  directionLo := (135012586505767560093/25000000000000000000)
  directionHi := (540050346023070240373/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree127.table
  base := (23701126778817791292064951488665283271461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-6496088357251735178217733120952780000000000000)
      constant := (266810726552190568043840214163576830754767163501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree127.table
  base := (11850563389402272113014305595009009597897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3282293638293007833562978135862665000000000000)
      constant := (136199678986164106781724501225461655090064140977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135012586505767560093/25000000000000000000)
  centralHi := (540050346023070240373/100000000000000000000)
  directionLo := (108437833528963691947/20000000000000000000)
  directionHi := (67773645955602307467/12500000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree128.table
  base := (305950722287067101366722962192395335997/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3273232363924378603534173813555745000000000000)
      constant := (135510875106217007353812521313784139457678523080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree128.table
  base := (24476057782954550460511414955407110437507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-6615503008752598959668761511354690000000000000)
      constant := (276698070530104269655024373759368390087728900987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108437833528963691947/20000000000000000000)
  centralHi := (67773645955602307467/12500000000000000000)
  directionLo := (544319585154828150651/100000000000000000000)
  directionHi := (136079896288707037663/25000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree129.table
  base := (25260343409339364918312495420512566457317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-6596841098445779235918962133270200000000000000)
      constant := (275265767335077389079818202875045952659751569197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree129.table
  base := (1010413736373221267319420641204485724749/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-6666418740919182252211566750984050000000000000)
      constant := (281030459111619569598601375534922785491004427725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544319585154828150651/100000000000000000000)
  centralHi := (136079896288707037663/25000000000000000000)
  directionLo := (273220848424341225439/50000000000000000000)
  directionHi := (546441696848682450879/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree130.table
  base := (1628373977981197328497694052132484089241/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3323608734521400632384788319714455000000000000)
      constant := (139771388959355580684352178870748437940217763848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree130.table
  base := (6513495911922986209551366796981068167993/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-1679333618271441386188592997653352500000000000)
      constant := (71349130928866148701878242293980971203710724513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273220848424341225439/50000000000000000000)
  centralHi := (546441696848682450879/100000000000000000000)
  directionLo := (109711119824129136503/20000000000000000000)
  directionHi := (137138899780161420629/25000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree131.table
  base := (6714244621997755587991929088929416192673/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3348796919819911646810095572793810000000000000)
      constant := (141926390980975763559226811931906793798351408786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree131.table
  base := (26856978487985133691737184533043517904359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-6768250205252348837297177230242770000000000000)
      constant := (289796264340255549983995412940869882847873877119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109711119824129136503/20000000000000000000)
  centralHi := (137138899780161420629/25000000000000000000)
  directionLo := (550661386514756169913/100000000000000000000)
  directionHi := (275330693257378084957/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree132.table
  base := (5533865584068682409884130201260250755899/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-6747970210236845322470805651746330000000000000)
      constant := (288195779463439756569201346681646850871463471295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree132.table
  base := (13834663960169302231732387630602922552617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3409582968709466064919991234936065000000000000)
      constant := (147114840492316856426329887614144536863064756497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (550661386514756169913/100000000000000000000)
  centralHi := (275330693257378084957/50000000000000000000)
  directionLo := (276379575887083616343/50000000000000000000)
  directionHi := (552759151774167232687/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree133.table
  base := (14245515967531189507621215811714418477397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (24751)
      previous := (0)
      next := (14575)
      square := (408373759810671081230126770635000000000000)
      linear := (-69370883477896605625728777121480000000000000)
      constant := (2985426228794301684857909529376337051503008173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree133.table
  base := (3561378991882306782094048556718939324693/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (12508)
      previous := (0)
      next := (7155)
      square := (204186879905335540615063385317500000000000)
      linear := (-35051437089722017461136671987252500000000000)
      constant := (1523963130853391861861786739193297001126125274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276379575887083616343/50000000000000000000)
  centralHi := (552759151774167232687/100000000000000000000)
  directionLo := (138712246472202303001/25000000000000000000)
  directionHi := (110969797177761842401/20000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree134.table
  base := (14661045261313574993291007427815678110633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3424361475715444690086017332031875000000000000)
      constant := (148490377417923252003201452498788287750825636753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree134.table
  base := (29322090522623946119370719279846137118231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-6920997401752098714925592949130850000000000000)
      constant := (303197542326838382445904896155440422159090433071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138712246472202303001/25000000000000000000)
  centralHi := (110969797177761842401/20000000000000000000)
  directionLo := (139232744535360458521/25000000000000000000)
  directionHi := (111386195628288366817/20000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree135.table
  base := (30162503673685840140740889296462354651157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-6899099322027911409022649170222460000000000000)
      constant := (301422732704167370461303614229238787456539900637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree135.table
  base := (30162503673683224897235874604137857627167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-6971913133918682007468398188760210000000000000)
      constant := (307731987022067246720380599913908738861660893047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139232744535360458521/25000000000000000000)
  centralHi := (111386195628288366817/20000000000000000000)
  directionLo := (559005216152162859153/100000000000000000000)
  directionHi := (279502608076081429577/50000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree136.table
  base := (3876533922381412873642921650797718293697/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3474737846312466718936631838190585000000000000)
      constant := (152948852012769818225471608081777814974650995108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree136.table
  base := (62024542758098336683314345134185054719/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-1755707216521316325002800857097392500000000000)
      constant := (78075026932921718263726319503865755639572234875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (559005216152162859153/100000000000000000000)
  centralHi := (279502608076081429577/50000000000000000000)
  directionLo := (280535892960717897263/50000000000000000000)
  directionHi := (561071785921435794527/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree137.table
  base := (3187139362969711048417792157244478286439/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3499926031610977733361939091269940000000000000)
      constant := (155202834399360447696210205066700187429118751995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree137.table
  base := (15935696814847684104081384864835228398283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3536872299125924296277004334009465000000000000)
      constant := (158450952227227428796150790728655205671968070403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280535892960717897263/50000000000000000000)
  centralHi := (561071785921435794527/100000000000000000000)
  directionLo := (112626154374339291079/20000000000000000000)
  directionHi := (140782692967924113849/25000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree138.table
  base := (32739870416753658294348532238941873402349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-7050228433818977495574492688698590000000000000)
      constant := (314946627022490326075943754906058998396972718709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree138.table
  base := (1309594816670089453705554623275540015777/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-7124660330418431885096813907648290000000000000)
      constant := (321537377189150381349449132623456315082789051425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112626154374339291079/20000000000000000000)
  centralHi := (140782692967924113849/25000000000000000000)
  directionLo := (565182256887595325451/100000000000000000000)
  directionHi := (141295564221898831363/25000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree139.table
  base := (1680885086575219572529575439870226874853/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3550302402207999762212553597428650000000000000)
      constant := (159760289347824086579508177122086745222816417730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree139.table
  base := (33617701731503230990609490603473193898961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-7175576062585015177639619147277650000000000000)
      constant := (326206525934573690802720104593160773881446891001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (565182256887595325451/100000000000000000000)
  centralHi := (141295564221898831363/25000000000000000000)
  directionLo := (283613161177464995839/50000000000000000000)
  directionHi := (567226322354929991679/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree140.table
  base := (345048875653821457969768050567900139289/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (24751)
      previous := (0)
      next := (14575)
      square := (408373759810671081230126770635000000000000)
      linear := (-72969195663398179115058384704245000000000000)
      constant := (3307423712418522893878080006734311574563140050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree140.table
  base := (34504887565381198789851860609939161730669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (50032)
      previous := (0)
      next := (28620)
      square := (816747519621342162460253541270000000000000)
      linear := (-147479424382685683064947436467490000000000000)
      constant := (6753252054888685599922138594458919105301449221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283613161177464995839/50000000000000000000)
  centralHi := (567226322354929991679/100000000000000000000)
  directionLo := (569263048198319394083/100000000000000000000)
  directionHi := (142315762049579848521/25000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree141.table
  base := (35401427909965600894115314144009094882283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-7201357545610043582126336207174720000000000000)
      constant := (328767462385432418432452258094307258328692314403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree141.table
  base := (4425178488745603514592094608245272679323/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-1819351881729545440681307406634092500000000000)
      constant := (83911462863226743594163810733371585153709394086) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569263048198319394083/100000000000000000000)
  centralHi := (142315762049579848521/25000000000000000000)
  directionLo := (114258502583533846603/20000000000000000000)
  directionHi := (71411564114708654127/12500000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree142.table
  base := (18153661378487920112485961730304530524011/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3625866958103532805488475356666715000000000000)
      constant := (166720197199880089653948188307022015885855398051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree142.table
  base := (7261464551395041930809076440404177327819/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-7328323259084765055268034866165730000000000000)
      constant := (340416028223518313386800147546948596857891674895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114258502583533846603/20000000000000000000)
  centralHi := (71411564114708654127/12500000000000000000)
  directionLo := (1119755456295850793/195312500000000000)
  directionHi := (573314793623475606017/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree143.table
  base := (465282151228412684272113844430436642807/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3651055143402043819913782609746070000000000000)
      constant := (169073159929439074631799524919206395448103931480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree143.table
  base := (37222572098272500233712313248149842622809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-7379238991251348347810840105795090000000000000)
      constant := (345219881000259235273123812030808392488446053569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1119755456295850793/195312500000000000)
  centralHi := (573314793623475606017/100000000000000000000)
  directionLo := (71916245758876474387/12500000000000000000)
  directionHi := (575329966071011795097/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree144.table
  base := (9536793981463276492594586599432998243151/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3676243328700554834339089862825425000000000000)
      constant := (171442619380842323596381377071136674622371093582) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree144.table
  base := (9536793981463171545741821730808660463653/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-1857538680854482910088411336356112500000000000)
      constant := (87514352445507014897423116151079514834877662573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71916245758876474387/12500000000000000000)
  centralHi := (575329966071011795097/100000000000000000000)
  directionLo := (577338104693441086963/100000000000000000000)
  directionHi := (144334526173360271741/25000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree145.table
  base := (4885141778980598132004852652406869765319/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3701431513999065848764397115904780000000000000)
      constant := (173828575553548127760244677834566367095473089916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree145.table
  base := (7816226846368888513518068754097816943129/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-7481070455584514932896450585053810000000000000)
      constant := (354928614567741369301235135827886088109346093445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (577338104693441086963/100000000000000000000)
  centralHi := (144334526173360271741/25000000000000000000)
  directionLo := (144834820658474144079/25000000000000000000)
  directionHi := (579339282633896576317/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree146.table
  base := (40024447008506364292259769356561875203889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-7453239398595153726379408737968270000000000000)
      constant := (352462056894047400609169759355369773064938485849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree146.table
  base := (40024447008506084882211666916537904505313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-7531986187751098225439255824683170000000000000)
      constant := (359833495356333591210748218737244233714015786633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144834820658474144079/25000000000000000000)
  centralHi := (579339282633896576317/100000000000000000000)
  directionLo := (116266714355313413939/20000000000000000000)
  directionHi := (567708566188053779/97656250000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree147.table
  base := (40977114248222837824116514971387283256009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (49502)
      previous := (0)
      next := (29150)
      square := (816747519621342162460253541270000000000000)
      linear := (-153135015697799505208775984574020000000000000)
      constant := (7291835839214080519141352610080199378666129281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree147.table
  base := (204885571241113049427342841029133439953/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (12508)
      previous := (0)
      next := (7155)
      square := (204186879905335540615063385317500000000000)
      linear := (-38688275101620824071337046246492500000000000)
      constant := (1861081898707941778862690365163131791641398850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116266714355313413939/20000000000000000000)
  centralHi := (567708566188053779/97656250000000000)
  directionLo := (583321042776826468759/100000000000000000000)
  directionHi := (14583026069420661719/2500000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree148.table
  base := (20969567971751504179251041320914956164299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3776996069894598892040318875142845000000000000)
      constant := (181085424394196397060069187040383405481410278659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree148.table
  base := (41939135943502822417979523729520322357091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-7633817652084264810524866303941890000000000000)
      constant := (369744284937979266047319981999738906689552362331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (583321042776826468759/100000000000000000000)
  centralHi := (14583026069420661719/2500000000000000000)
  directionLo := (292650882545221180881/50000000000000000000)
  directionHi := (585301765090442361763/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree149.table
  base := (42910512086976696847829546378566231104923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-7604368510386219812931252256444400000000000000)
      constant := (367074734893741507841517135835784417115512706643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree149.table
  base := (10727628021744136293510832705465240919531/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-1921183346062712025766917885892812500000000000)
      constant := (93687548432246796201728052696105471225405166371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292650882545221180881/50000000000000000000)
  centralHi := (585301765090442361763/100000000000000000000)
  directionLo := (11745516140037959709/2000000000000000000)
  directionHi := (587275807001897985451/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree150.table
  base := (43891242671392032240732548972414902646599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-7654744880983241841781866762603110000000000000)
      constant := (372011614436537931818681446386353659615180532959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree150.table
  base := (10972810667847977131054536610841998152831/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-1933912279104357848902619195800152500000000000)
      constant := (94947444629695547587049498302056403467753811671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11745516140037959709/2000000000000000000)
  centralHi := (587275807001897985451/100000000000000000000)
  directionLo := (589243235651860231687/100000000000000000000)
  directionHi := (73655404456482528961/12500000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree151.table
  base := (44881327689612818513932302730269232505231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-7705121251580263870632481268761820000000000000)
      constant := (376981487415799832894791190115607639931252500071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree151.table
  base := (44881327689612717605897284275336950248197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-7786564848584014688153282022829970000000000000)
      constant := (384863039306382049674093282359557293169112083277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (589243235651860231687/100000000000000000000)
  centralHi := (73655404456482528961/12500000000000000000)
  directionLo := (591204117063824959561/100000000000000000000)
  directionHi := (295602058531912479781/50000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree152.table
  base := (22940383567307988157036869685785464987587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3877748811088642949741547887460265000000000000)
      constant := (190992176915280273702285611035171017186356462267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree152.table
  base := (9176153426923178802618872578079508338063/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-7837480580750597980696087262459330000000000000)
      constant := (389969976090820099249719706712372248035796646915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (591204117063824959561/100000000000000000000)
  centralHi := (295602058531912479781/50000000000000000000)
  directionLo := (593158516169969530219/100000000000000000000)
  directionHi := (29657925808498476511/5000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree153.table
  base := (46889560999489056647348560647151061686551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-7805873992774307928333710281079240000000000000)
      constant := (387020213679868638956064774271242981781598566191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree153.table
  base := (23444780499744494762612545382183094951357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3944198156458590636619446251044345000000000000)
      constant := (197555294435572451394773911898495163372199728837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593158516169969530219/100000000000000000000)
  centralHi := (29657925808498476511/5000000000000000000)
  directionLo := (14877662420906030109/2500000000000000000)
  directionHi := (595106496836241204361/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree154.table
  base := (748557957459809752476120163816011490553/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (24751)
      previous := (0)
      next := (14575)
      square := (408373759810671081230126770635000000000000)
      linear := (-80165820034401326093717599869775000000000000)
      constant := (4000908846559056793783010750638533640862828064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree154.table
  base := (4790770927742776941806169149132584921909/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (25016)
      previous := (0)
      next := (14310)
      square := (408373759810671081230126770635000000000000)
      linear := (-81013388215140454752874466752225000000000000)
      constant := (4084539567820611414509185696338007155228211905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14877662420906030109/2500000000000000000)
  centralHi := (595106496836241204361/100000000000000000000)
  directionLo := (29852406094335441377/5000000000000000000)
  directionHi := (597048121886708827541/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree155.table
  base := (48935211961733907639381849234214895240593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-7906626733968351986034939293396660000000000000)
      constant := (397190913678395357397133297352232184895810461113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree155.table
  base := (48935211961733862998545879569488743154913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-7990227777250347858324502981347410000000000000)
      constant := (405492842415723176306213594570023800096585380233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29852406094335441377/5000000000000000000)
  centralHi := (597048121886708827541/100000000000000000000)
  directionLo := (119796690625440814541/20000000000000000000)
  directionHi := (299491726563602036353/50000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree156.table
  base := (24986034522906257751090088754326909920817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-3978501552282687007442776899777685000000000000)
      constant := (201162876912892150033154759367561280208411172697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree156.table
  base := (2498603452290623954952446639316210976359/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-2010285877354232787716827055244192500000000000)
      constant := (102683620794536740547846106957408172974985145595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119796690625440814541/20000000000000000000)
  centralHi := (299491726563602036353/50000000000000000000)
  directionLo := (300456275684138704741/50000000000000000000)
  directionHi := (600912551368277409483/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree157.table
  base := (51018280523170214040576776927827667829913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-8007379475162396043736168305714080000000000000)
      constant := (407493587404060631089496269808365230527777055233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree157.table
  base := (25509140261585092178113359589877752750831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-4046029620791757221705056730303065000000000000)
      constant := (208004899966398756807924324176279583766377129671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300456275684138704741/50000000000000000000)
  centralHi := (600912551368277409483/100000000000000000000)
  directionLo := (602835476447492922659/100000000000000000000)
  directionHi := (30141773822374646133/5000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree158.table
  base := (10414769277482553277945504337985985449171/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-8057755845759418072586782811872790000000000000)
      constant := (412694414412344241310379540252473745116046728055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree158.table
  base := (1041476927748254843701386477480652360969/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-4071487486875048867976459350117745000000000000)
      constant := (210659396339397360730904453222695061790403353225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (602835476447492922659/100000000000000000000)
  centralHi := (30141773822374646133/5000000000000000000)
  directionLo := (604752287251085105147/100000000000000000000)
  directionHi := (151188071812771276287/25000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree159.table
  base := (10627753326448606035208937361211417303823/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25970000000000000000000000000000000000000000
      center := (45766)
      previous := (0)
      next := (26950)
      square := (755106197385769169067026858910000000000000)
      linear := (-152983626723706417008252779585500000000000000)
      constant := (7885438393391856335009742302117932753690141655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree159.table
  base := (26569383316121505220157393536990812020427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12985000000000000000000000000000000000000000
      center := (23128)
      previous := (0)
      next := (13230)
      square := (377553098692884584533513429455000000000000)
      linear := (-77300855716195104042412489998725000000000000)
      constant := (4025108126559168309313671704716585138817048919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (604752287251085105147/100000000000000000000)
  centralHi := (151188071812771276287/25000000000000000000)
  directionLo := (606663041734999800809/100000000000000000000)
  directionHi := (60666304173499980081/10000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree160.table
  base := (27106520625729455963280671185368569061739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-4079254293476731065144005912095105000000000000)
      constant := (211597524357739701038597016944288115214226817699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree160.table
  base := (54213041251458895835285554193135865779103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-8244806438083264321038529179494210000000000000)
      constant := (432037806141375209270097945825427013701701516023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (606663041734999800809/100000000000000000000)
  centralHi := (60666304173499980081/10000000000000000000)
  directionLo := (152141949236335141853/25000000000000000000)
  directionHi := (608567796945340567413/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree161.table
  base := (6912083779868922047740918110290725053479/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (24751)
      previous := (0)
      next := (14575)
      square := (408373759810671081230126770635000000000000)
      linear := (-83764132219902899583047207452540000000000000)
      constant := (4372396489884045270951840844691237836700890044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree161.table
  base := (55296670238951363262616434818099580189669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (50032)
      previous := (0)
      next := (28620)
      square := (816747519621342162460253541270000000000000)
      linear := (-169300452454078522726149682022930000000000000)
      constant := (8927506670535999453247801829553201720752780221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152141949236335141853/25000000000000000000)
  centralHi := (608567796945340567413/100000000000000000000)
  directionLo := (610466609038240867139/100000000000000000000)
  directionHi := (30523330451912043357/5000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree162.table
  base := (56389653588702508928286809330024548077979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-8259261328147506187989240836507630000000000000)
      constant := (433827656728411177398409710816974348822001107539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree162.table
  base := (11277930717740499646488655390812239622121/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-8346637902416430906124139658752930000000000000)
      constant := (442891523559109820836082840423279777369141782805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (610466609038240867139/100000000000000000000)
  centralHi := (30523330451912043357/5000000000000000000)
  directionLo := (612359533299181669483/100000000000000000000)
  directionHi := (153089883324795417371/25000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree163.table
  base := (57491991294783629431320784863440420939101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-8309637698744528216839855342666340000000000000)
      constant := (439193450873987595150214163286276415478478800741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree163.table
  base := (57491991294783620711596870924026505181057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-8397553634583014198666944898382290000000000000)
      constant := (448368896249096722702474154961794532199625866537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (612359533299181669483/100000000000000000000)
  centralHi := (153089883324795417371/25000000000000000000)
  directionLo := (307123312080886633331/50000000000000000000)
  directionHi := (614246624161773266663/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree164.table
  base := (11720736670270691164155046700788198233987/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-8360014069341550245690469848825050000000000000)
      constant := (444592238444561689903261924146230561965621023335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree164.table
  base := (1465092083783836217808378953410975446683/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-2112117341687399372802437534502912500000000000)
      constant := (113469986231355169728560357144262680714568948030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307123312080886633331/50000000000000000000)
  centralHi := (614246624161773266663/100000000000000000000)
  directionLo := (61612793522601935319/10000000000000000000)
  directionHi := (616127935226019353191/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree165.table
  base := (29862364876328157918005996148773829825087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-4205195219969286137270542177491880000000000000)
      constant := (225012009719670622585963248004844109960954799767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree165.table
  base := (933198902385254844395708459024818589653/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (612892)
      previous := (0)
      next := (350595)
      square := (10005157115361441490138105880557500000000000)
      linear := (-2124846274729045195938138844410252500000000000)
      constant := (114856167396822368248755535431939010887974857168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61612793522601935319/10000000000000000000)
  centralHi := (616127935226019353191/100000000000000000000)
  directionLo := (618003519276080706753/100000000000000000000)
  directionHi := (309001759638040353377/50000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree166.table
  base := (12171026098604081080525096763667079850447/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-8460766810535594303391698861142470000000000000)
      constant := (455488793857545588171602620794167642688476877635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree166.table
  base := (60855130493020400679060673189362621104279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-8550300831082764076295360617270370000000000000)
      constant := (465003070233922432167767366187028500531414065839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (618003519276080706753/100000000000000000000)
  centralHi := (309001759638040353377/50000000000000000000)
  directionLo := (619873428297555125653/100000000000000000000)
  directionHi := (309936714148777562827/50000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree167.table
  base := (30997442783428046083567601109167175540517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1212799)
      previous := (0)
      next := (714175)
      square := (20010314230722882980276211761115000000000000)
      linear := (-4255571590566308166121156683650590000000000000)
      constant := (230493280849202678157762444097124205458572300397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree167.table
  base := (6199488556685608831683790252349725592153/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1225784)
      previous := (0)
      next := (701190)
      square := (20010314230722882980276211761115000000000000)
      linear := (-4300608281624673684419082928449865000000000000)
      constant := (235307573432275096925937438888666962901147655365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (619873428297555125653/100000000000000000000)
  centralHi := (309936714148777562827/50000000000000000000)
  directionLo := (310868856747144813413/50000000000000000000)
  directionHi := (621737713494289626827/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree168.table
  base := (15785998742163565692820329607925925562113/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (24751)
      previous := (0)
      next := (14575)
      square := (408373759810671081230126770635000000000000)
      linear := (-87362444405404473072376815035305000000000000)
      constant := (4760380846542472140121929153851827849807950834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree168.table
  base := (7892999371081782454114674219370965717187/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (12508)
      previous := (0)
      next := (7155)
      square := (204186879905335540615063385317500000000000)
      linear := (-44143532119469033986637607635352500000000000)
      constant := (2429902548359257541737893425059226085399156566) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell234.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310868856747144813413/50000000000000000000)
  centralHi := (621737713494289626827/100000000000000000000)
  directionLo := (124719285060948057289/20000000000000000000)
  directionHi := (311798212652370143223/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree169.table
  base := (64302458692984712499660384217249776058503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2425598)
      previous := (0)
      next := (1428350)
      square := (40020628461445765960552423522230000000000000)
      linear := (-8611895922326660389943542379618600000000000000)
      constant := (472081077645068909613642281424493658926468411423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree169.table
  base := (64302458692984709941680187527217929469373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2451568)
      previous := (0)
      next := (1402380)
      square := (40020628461445765960552423522230000000000000)
      linear := (-8703048027582513953923776336158450000000000000)
      constant := (481940328074767866350890787605055923030093969093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell234.Kernel169
