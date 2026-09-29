import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell127.Parameters
import ForestUnimodality.BinomialMassData.Q4657_8862.Batch000_049
import ForestUnimodality.BinomialMassData.Q4657_8862.Batch050_099
import ForestUnimodality.BinomialMassData.Q4657_8862.Batch100_149
import ForestUnimodality.BinomialMassData.Q4657_8862.Batch150_199
import ForestUnimodality.BinomialMassData.Q111_211.Batch000_049
import ForestUnimodality.BinomialMassData.Q111_211.Batch050_099
import ForestUnimodality.BinomialMassData.Q111_211.Batch100_149
import ForestUnimodality.BinomialMassData.Q111_211.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree000.table
  base := (729328481836543586658194727/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (719782904477117985164724700000000000000)
      linear := (-48164742134287679906079482000000000000)
      constant := (729328481836543586658194727000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree000.table
  base := (729328481836543586658194727/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (719782904477117985164724700000000000000)
      linear := (-48164742134287679906079482000000000000)
      constant := (729328481836543586658194727000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree001.table
  base := (204964378648484687975048336909568194632959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-2256927924760230216442583384302386000000000000)
      constant := (1150406113041650614131751172427408630749999922514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree001.table
  base := (102396809996467736537818574342267171114719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-35860413296077782458184599015522000000000000)
      constant := (18245230023002550116047177853744928900793618396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (3120750519209934493/6250000000000000000)
  directionHi := (49932008307358951889/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree002.table
  base := (61329470899952297977347360737345751070853/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-625537467570448751381136742523298000000000000)
      constant := (98635040451233194809118984279446832603316070868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree002.table
  base := (244967337013541222561430001452414174737713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-69576484107594943119270633412922000000000000)
      constant := (10943920724695173355940443961873575473497720473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3120750519209934493/6250000000000000000)
  centralHi := (49932008307358951889/100000000000000000000)
  directionLo := (35307261672396539619/50000000000000000000)
  directionHi := (70614523344793079239/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree003.table
  base := (31447874290263477249573542228196106241573/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-722288513469561366988147890113754000000000000)
      constant := (49584356632312598943219326886790991609337503655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree003.table
  base := (15695995184341780551494665409520858285463/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-103292554919112103780356667810322000000000000)
      constant := (7071214221791948710841112006874847317270982230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35307261672396539619/50000000000000000000)
  centralHi := (70614523344793079239/100000000000000000000)
  directionLo := (43242387656148481201/50000000000000000000)
  directionHi := (86484775312296962403/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree004.table
  base := (21535076505699818777803398219717862738847/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-8622430969458963346118704824384486000000000000)
      constant := (311214585299576268158669734703205458603805295405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree004.table
  base := (107468002497890212531367756894776649844527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-137008625730629264441442702207722000000000000)
      constant := (4930990327567679890236778223363239227728186567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43242387656148481201/50000000000000000000)
  centralHi := (86484775312296962403/100000000000000000000)
  directionLo := (3120750519209934493/3125000000000000000)
  directionHi := (99864016614717903777/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree005.table
  base := (78014396881581262333769479873160442677909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-10744265317691874389344078637745186000000000000)
      constant := (233109390764838694243327415851427222313180755107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree005.table
  base := (38930864170627617501318726271543634573151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-170724696542146425102528736605122000000000000)
      constant := (3693833468760224343688187788127898309662511342) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3120750519209934493/3125000000000000000)
  centralHi := (99864016614717903777/100000000000000000000)
  directionLo := (55825682414169414517/50000000000000000000)
  directionHi := (22330272965667765807/20000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree006.table
  base := (59028851725722315392910412732493551553461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-1429566629547198381396605827900654000000000000)
      constant := (20673549528192551610131673485035531860981460267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree006.table
  base := (58914120394793092502464259452087014854097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-204440767353663585763614771002522000000000000)
      constant := (2948947978627998726836417649387097988319252537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55825682414169414517/50000000000000000000)
  centralHi := (22330272965667765807/20000000000000000000)
  directionLo := (122307942185440191067/100000000000000000000)
  directionHi := (30576985546360047767/25000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree007.table
  base := (5757410604268732492271737615089362555513/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-2141133430593956639399260894923798000000000000)
      constant := (22429040492139522127291508049566728744047587656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree007.table
  base := (45970331342018589760112722858681799416449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-238156838165180746424700805399922000000000000)
      constant := (2489095399793765661033054625633126391819725929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122307942185440191067/100000000000000000000)
  centralHi := (30576985546360047767/25000000000000000000)
  directionLo := (132107676443282975807/100000000000000000000)
  directionHi := (2064182444426296497/1562500000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree008.table
  base := (36685920239081160453626365537796221126511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-17109768362390607519020200077827286000000000000)
      constant := (139146360549285489864886532225255178328723962553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree008.table
  base := (9153704385772090596231317680721974226719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-271872908976697907085786839797322000000000000)
      constant := (2206733313868058720241632952073868058191026396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132107676443282975807/100000000000000000000)
  centralHi := (2064182444426296497/1562500000000000000)
  directionLo := (141229046689586158477/100000000000000000000)
  directionHi := (70614523344793079239/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree009.table
  base := (92506804991402683746338924317083291533/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-305263535089262199400723395098222000000000000)
      constant := (2044864293151036319860023297855654871149021760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree009.table
  base := (29543960698115564993364191619837862388239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-305588979788215067746872874194722000000000000)
      constant := (2043823330521615661141670178362799471386788519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141229046689586158477/100000000000000000000)
  centralHi := (70614523344793079239/50000000000000000000)
  directionLo := (9362251557629803479/6250000000000000000)
  directionHi := (29959204984415371133/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree010.table
  base := (24066166078821827625383792349445137457171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-21353437058856429605470947704548686000000000000)
      constant := (123962680739666617647214185182158468778034735733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree010.table
  base := (120088611286550630418347546446096345081/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-339305050599732228407958908592122000000000000)
      constant := (1967418193479232710403310401414551075870240200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9362251557629803479/6250000000000000000)
  centralHi := (29959204984415371133/20000000000000000000)
  directionLo := (157898874397703145361/100000000000000000000)
  directionHi := (78949437198851572681/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree011.table
  base := (4907773071804392767479752197761464579303/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-23475271407089340648696321517909386000000000000)
      constant := (123301874967756772557990208668699873462857513476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree011.table
  base := (2448800291989870551219040817065167369823/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-373021121411249389069044942989522000000000000)
      constant := (1957674898171817937869429829232308531775118264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157898874397703145361/100000000000000000000)
  centralHi := (78949437198851572681/50000000000000000000)
  directionLo := (165605736584418467479/100000000000000000000)
  directionHi := (4140143414610461687/2500000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree012.table
  base := (16010837650795323398472059307816697545081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-2844122861702472410213521703474454000000000000)
      constant := (14004613466924509490586767893553178339831858407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree012.table
  base := (124816498606186845184195234997689527621/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-406737192222766549730130977386922000000000000)
      constant := (2001883183828429701532893142046377338779461248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165605736584418467479/100000000000000000000)
  centralHi := (4140143414610461687/2500000000000000000)
  directionLo := (34593910124918784961/20000000000000000000)
  directionHi := (86484775312296962403/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree013.table
  base := (13011453530493288927692728585770074085337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-27718940103555162735147069144630786000000000000)
      constant := (131637627839698833265124891334370074506257180351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree013.table
  base := (12982465936102539604023571898182582737599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-440453263034283710391217011784322000000000000)
      constant := (2091424462537648585966040024452272766060645079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34593910124918784961/20000000000000000000)
  centralHi := (86484775312296962403/50000000000000000000)
  directionLo := (180032416239076578101/100000000000000000000)
  directionHi := (90016208119538289051/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree014.table
  base := (5247562368952113284042399634834578516789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-4262967778826867682624634708284498000000000000)
      constant := (19957663952813936133308300099272406862627335242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree014.table
  base := (10470667922765333845766143868561262784957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-474169333845800871052303046181722000000000000)
      constant := (2220172789095079408924534830468323980449070597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180032416239076578101/100000000000000000000)
  centralHi := (90016208119538289051/50000000000000000000)
  directionLo := (186828467719687428179/100000000000000000000)
  directionHi := (9341423385984371409/5000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree015.table
  base := (8360376464162435325977341529024205325403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-3551400977780109424621979641261354000000000000)
      constant := (16661662423832180262356606744849466517045868741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree015.table
  base := (8339783986884241624685935785529040130289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-507885404657318031713389080579122000000000000)
      constant := (2383616681627059004062125791783868395640596569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186828467719687428179/100000000000000000000)
  centralHi := (9341423385984371409/5000000000000000000)
  directionLo := (9669291830854580577/5000000000000000000)
  directionHi := (193385836617091611541/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree016.table
  base := (3265300238452217098446175294838989072841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-4869206164036270837831884369244698000000000000)
      constant := (23168099677421800809693708653702727385215174898) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree016.table
  base := (1628326511034842198910621953987227774491/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-541601475468835192374475114976522000000000000)
      constant := (2578349923711581364143014496167813470992455244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9669291830854580577/5000000000000000000)
  centralHi := (193385836617091611541/100000000000000000000)
  directionLo := (3120750519209934493/1562500000000000000)
  directionHi := (199728033229435807553/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree017.table
  base := (4946988289171777772352887512604069583813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-36206277496486806908048564398073586000000000000)
      constant := (176203908055270255127157087005951666262279130099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree017.table
  base := (4932503657887222203221918210321921478497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-575317546280352353035561149373922000000000000)
      constant := (2801757777578841530395019514250716266144164937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3120750519209934493/1562500000000000000)
  centralHi := (199728033229435807553/100000000000000000000)
  directionLo := (25734368043807431891/12500000000000000000)
  directionHi := (205874944350459455129/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree018.table
  base := (712781393460867185985642730909295748441/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-4258679093857746439030437579048254000000000000)
      constant := (21323177828061684843191809815572188460571961635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree018.table
  base := (3551809069789780213691115170211258813413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-609033617091869513696647183771322000000000000)
      constant := (3051811521059872441662708975654371453631960173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25734368043807431891/12500000000000000000)
  centralHi := (205874944350459455129/100000000000000000000)
  directionLo := (42368714006875847543/20000000000000000000)
  directionHi := (52960892508594809429/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree019.table
  base := (2345706158074013035301704520202151179109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-40449946192952628994499312024794986000000000000)
      constant := (209190782003115044171232706911723782276642042707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree019.table
  base := (72988392873575882189460390860434312711/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-642749687903386674357733218168722000000000000)
      constant := (3326926486685587003473609240739134673158605792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42368714006875847543/20000000000000000000)
  centralHi := (52960892508594809429/25000000000000000000)
  directionLo := (27206072282476383851/12500000000000000000)
  directionHi := (217648578259811070809/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree020.table
  base := (1264416587371931532105282373661818301177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-42571780541185540037724685838155686000000000000)
      constant := (227972003843636012600391361821207682192962176671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree020.table
  base := (251208598585212660290896699091026706353/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-676465758714903835018819252566122000000000000)
      constant := (3625859685023632577351490022139597999967709565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27206072282476383851/12500000000000000000)
  centralHi := (217648578259811070809/100000000000000000000)
  directionLo := (55825682414169414517/25000000000000000000)
  directionHi := (223302729656677658069/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree021.table
  base := (298038027937014961678217244755856061389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-709422458562197636205556502405022000000000000)
      constant := (3939532686201444041590350610340957467709099669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree021.table
  base := (72774148478901752451309749458604375679/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-710181829526420995679905286963522000000000000)
      constant := (3947633624627380603045851789585648101638419036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55825682414169414517/25000000000000000000)
  centralHi := (223302729656677658069/100000000000000000000)
  directionLo := (45763441533927245081/20000000000000000000)
  directionHi := (114408603834818112703/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree022.table
  base := (-285381078508916282544665243259345025669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-46815449237651362124175433464877086000000000000)
      constant := (269797833185968837577654159110046150214135996826) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree022.table
  base := (-576503882996723788012140112389844359099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-743897900337938156340991321360922000000000000)
      constant := (4291478392360984415241531182001375739288553421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45763441533927245081/20000000000000000000)
  centralHi := (114408603834818112703/50000000000000000000)
  directionLo := (46840375736894166993/20000000000000000000)
  directionHi := (117100939342235417483/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree023.table
  base := (-1355652577272905552876059433833208047519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-6991040512269181881057258182605398000000000000)
      constant := (41822212525482829499897307473601649700647659409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree023.table
  base := (-1360392409199703879134647286966435778519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-777613971149455317002077355758322000000000000)
      constant := (4656786990184244371640402113921473312704555601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46840375736894166993/20000000000000000000)
  centralHi := (117100939342235417483/50000000000000000000)
  directionLo := (23946549946274464909/10000000000000000000)
  directionHi := (239465499462744649091/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree024.table
  base := (-2067418759049747441435170485760129913183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-5673235326013020467847353454622054000000000000)
      constant := (35225919023990065916639352876787568792946257599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree024.table
  base := (-2071324263419567537019983829725000546661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-811330041960972477663163390155722000000000000)
      constant := (5043080582332989796153854265598141250662105619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23946549946274464909/10000000000000000000)
  centralHi := (239465499462744649091/100000000000000000000)
  directionLo := (122307942185440191067/50000000000000000000)
  directionHi := (48923176874176076427/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree025.table
  base := (-1357287167403671636441366178549803217821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-53180952282350095253851554904959186000000000000)
      constant := (342607304566426690026290111636823960578363298634) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree025.table
  base := (-135889342822426833240841901576649459473/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-845046112772489638324249424553122000000000000)
      constant := (5449981300791340177431804885633669788296051340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122307942185440191067/50000000000000000000)
  centralHi := (48923176874176076427/20000000000000000000)
  directionLo := (3120750519209934493/1250000000000000000)
  directionHi := (249660041536794759441/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree026.table
  base := (-3303841074493056566583010196524941408631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-55302786630583006297076928718319886000000000000)
      constant := (369458734354979022840415123285321770263419372687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree026.table
  base := (-3306479381124276992169824529878558146589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-878762183584006798985335458950522000000000000)
      constant := (5877190890794969799524746085752448712755711131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3120750519209934493/1250000000000000000)
  centralHi := (249660041536794759441/100000000000000000000)
  directionLo := (25460428471210033423/10000000000000000000)
  directionHi := (254604284712100334231/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree027.table
  base := (-768105345050650608008482475335094940951/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-6380513442090657482255811392408954000000000000)
      constant := (44174741476699253417917303776178906334687218515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree027.table
  base := (-1921345132842636334573761707002779384069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-912478254395523959646421493347922000000000000)
      constant := (6324473906230273109587474611801252518083728102) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25460428471210033423/10000000000000000000)
  centralHi := (254604284712100334231/100000000000000000000)
  directionLo := (32431790742111360901/12500000000000000000)
  directionHi := (259454325936890887209/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree028.table
  base := (-4328822810725418735398863585030306043179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-8506636475292689769075382335005898000000000000)
      constant := (60991052127209428467949217628854275701864649669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree028.table
  base := (-4330594594486506964363204038939002607949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-946194325207041120307507527745322000000000000)
      constant := (6791644468166681897518059098825012664891502571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32431790742111360901/12500000000000000000)
  centralHi := (259454325936890887209/100000000000000000000)
  directionLo := (132107676443282975807/50000000000000000000)
  directionHi := (52843070577313190323/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree029.table
  base := (-2386019768039597670866429557015564446321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-61668289675281739426753050158401986000000000000)
      constant := (457543524615902648472289669486798900965953187634) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree029.table
  base := (-1193372163223688575832399493309140922883/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-979910396018558280968593562142722000000000000)
      constant := (7278555822683381999118247224659972947889303828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132107676443282975807/50000000000000000000)
  centralHi := (52843070577313190323/20000000000000000000)
  directionLo := (26889209388633712323/10000000000000000000)
  directionHi := (268892093886337123231/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree030.table
  base := (-323299448344765070992298767112543581721/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1012541651166899213809181332885122000000000000)
      constant := (7767997141203234231399862571375629155171189744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree030.table
  base := (-103479499568845206905116578413878949917/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1013626466830075441629679596540122000000000000)
      constant := (7785092102206900305394389592889444763537262150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26889209388633712323/10000000000000000000)
  centralHi := (268892093886337123231/100000000000000000000)
  directionLo := (273488872914758456187/100000000000000000000)
  directionHi := (68372218228689614047/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree031.table
  base := (-172910700352961431430791217919046704501/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-65911958371747561513203797785123386000000000000)
      constant := (522452459645054867121751398107102337284524533664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree031.table
  base := (-1106821681110622483617440748063313160103/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1047342537641592602290765630937522000000000000)
      constant := (8311161823453842024419033196843648173995271685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273488872914758456187/100000000000000000000)
  centralHi := (68372218228689614047/25000000000000000000)
  directionLo := (11120386256729831047/4000000000000000000)
  directionHi := (17375603526140361011/6250000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree032.table
  base := (-5854723907287841001959702914302676790629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-68033792719980472556429171598484086000000000000)
      constant := (556744870156948457656996032832861495176077596333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree032.table
  base := (-5855511346579034575530977836222853040733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1081058608453109762951851665334922000000000000)
      constant := (8856692755003896049597077318675826359773526107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11120386256729831047/4000000000000000000)
  centralHi := (17375603526140361011/6250000000000000000)
  directionLo := (141229046689586158477/50000000000000000000)
  directionHi := (56491618675834463391/20000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree033.table
  base := (-3069411768672223440886086728926397108641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-7795069674245931511072727267982754000000000000)
      constant := (65806382129742462679109329338001452240566716546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree033.table
  base := (-3069732399646723136984180492553150678249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1114774679264626923612937699732322000000000000)
      constant := (9421627865555191973310974117917808357307352542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141229046689586158477/50000000000000000000)
  centralHi := (56491618675834463391/20000000000000000000)
  directionLo := (286837549789080773443/100000000000000000000)
  directionHi := (71709387447270193361/25000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree034.table
  base := (-3193229227800118474303024669318096132029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-72277461416446294642879919225205486000000000000)
      constant := (628987313739941760420395081531486433305348048266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree034.table
  base := (-1596745049155375674133040212348610340727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1148490750076144084274023734129722000000000000)
      constant := (10005922125102468961652467864630658076081972932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286837549789080773443/100000000000000000000)
  centralHi := (71709387447270193361/25000000000000000000)
  directionLo := (18196946153326622799/6250000000000000000)
  directionHi := (58230227690645192957/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree035.table
  base := (-1649608001001276291891330633051354267981/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-10628470823525600812300756148366598000000000000)
      constant := (95276034377392759877334930173776623638867844364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree035.table
  base := (-329942806686668218691496666333240930839/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1182206820887661244935109768527122000000000000)
      constant := (10609539979390156297638379562698325610362337620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18196946153326622799/6250000000000000000)
  centralHi := (58230227690645192957/20000000000000000000)
  directionLo := (147700872438364187227/50000000000000000000)
  directionHi := (59080348975345674891/20000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree036.table
  base := (-6775378657658225655872968504611957129847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-8502347790323568525481185205769654000000000000)
      constant := (78454493364750416603315617264582881396354571991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree036.table
  base := (-6775723156539115036069394918185691815967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1215922891699178405596195802924522000000000000)
      constant := (11232453355883791143516131465767846814661333193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147700872438364187227/50000000000000000000)
  centralHi := (59080348975345674891/20000000000000000000)
  directionLo := (9362251557629803479/3125000000000000000)
  directionHi := (299592049844153711329/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree037.table
  base := (-1729449880434686743577804889711563761651/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-11234709208735003967508005809326798000000000000)
      constant := (106637215307374736611740615838734938911631289844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree037.table
  base := (-1729519781165878854120678307355407521809/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1249638962510695566257281837321922000000000000)
      constant := (11874640089375019526681494239876333606886166044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9362251557629803479/3125000000000000000)
  centralHi := (299592049844153711329/100000000000000000000)
  directionLo := (303724549194542463793/100000000000000000000)
  directionHi := (151862274597271231897/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree038.table
  base := (-7026090366530055859811801561089736719687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-80764798809377938815781414478648286000000000000)
      constant := (788041331182763980060734723546971699384677349599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree038.table
  base := (-219572410396975442954990109805766367167/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1283355033322212726918367871719322000000000000)
      constant := (12536082678899304052165322710546635218155455776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303724549194542463793/100000000000000000000)
  centralHi := (151862274597271231897/50000000000000000000)
  directionLo := (153900785603123391411/50000000000000000000)
  directionHi := (307801571206246782823/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree039.table
  base := (-3550281884623334400076978237627133193941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-9209625906401205539889643143556554000000000000)
      constant := (92314670628046185442965484069531349643015738346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree039.table
  base := (-7100747555905138789253965832615686790499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1317071104133729887579453906116722000000000000)
      constant := (13216767306240276261677120978187775008400194021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153900785603123391411/50000000000000000000)
  centralHi := (307801571206246782823/100000000000000000000)
  directionLo := (77956322983867211433/25000000000000000000)
  directionHi := (311825291935468845733/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree040.table
  base := (-7141466601520641383569461518076248016023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-85008467505843760902232162105369686000000000000)
      constant := (874831928129346586008897192039197663810954321071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree040.table
  base := (-7141615456742512416344227184337688535021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1350787174945247048240539940514122000000000000)
      constant := (13916683060971565787098467009362981768732330059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77956322983867211433/25000000000000000000)
  centralHi := (311825291935468845733/100000000000000000000)
  directionLo := (157898874397703145361/50000000000000000000)
  directionHi := (315797748795406290723/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree041.table
  base := (-714899384094360524139666229989556912173/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-87130301854076671945457535918730386000000000000)
      constant := (920040461735923238120252917237387896129281896210) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree041.table
  base := (-1787278582156751594260881608436536719589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1384503245756764208901625974911522000000000000)
      constant := (14635821328572991609537634210352689794828712524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157898874397703145361/50000000000000000000)
  centralHi := (315797748795406290723/100000000000000000000)
  directionLo := (319720852616548454503/100000000000000000000)
  directionHi := (39965106577068556813/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree042.table
  base := (-7123299479375795389552590903060517754727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1416700574639834650614014440191922000000000000)
      constant := (15340590548448162307344556738794356689041799233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree042.table
  base := (-7123396947544758780996493001941261636491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1418219316568281369562712009308922000000000000)
      constant := (15374175307304874874215134034700097090681784189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319720852616548454503/100000000000000000000)
  centralHi := (39965106577068556813/12500000000000000000)
  directionLo := (323596398390740532837/100000000000000000000)
  directionHi := (161798199195370266419/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree043.table
  base := (-7064505138296730298377944216419696443077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-91373970550542494031908283545451786000000000000)
      constant := (1014081815451556500301723259489296385763439439629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree043.table
  base := (-3532291970099030978854442069819260983523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1451935387379798530223798043706322000000000000)
      constant := (16131739626745802824329040663846099363505145034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323596398390740532837/100000000000000000000)
  centralHi := (161798199195370266419/50000000000000000000)
  directionLo := (327426074870443122889/100000000000000000000)
  directionHi := (32742607487044312289/10000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree044.table
  base := (-6972706873186053690721162748101634661091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-13356543556967915010733379622687498000000000000)
      constant := (151844860716467354598807220088830436109282108301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree044.table
  base := (-6972770549167049115999974719135260514387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1485651458191315690884884078103722000000000000)
      constant := (16908510046600865349289511161201147066638976373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327426074870443122889/100000000000000000000)
  centralHi := (32742607487044312289/10000000000000000000)
  directionLo := (165605736584418467479/50000000000000000000)
  directionHi := (331211473168836934959/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree045.table
  base := (-1711995136901435523673142947256835844981/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-10624182138556479568706559019130354000000000000)
      constant := (123661513384390630815664992336459725517676825172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree045.table
  base := (-1712007993622481986510514973146129221349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1519367529002832851545970112501122000000000000)
      constant := (17704483218889161404522384774296234723745284684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165605736584418467479/50000000000000000000)
  centralHi := (331211473168836934959/100000000000000000000)
  directionLo := (334954094485016487103/100000000000000000000)
  directionHi := (5233657726328382611/1562500000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree046.table
  base := (-6690386077636003689196745415338853767609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-97739473595241227161584404985533886000000000000)
      constant := (1164200433730289248004746766534302896158973621793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree046.table
  base := (-3345213795611682852535472730333316031057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1553083599814350012207056146898522000000000000)
      constant := (18519656500173793107068266193079272873962622606) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334954094485016487103/100000000000000000000)
  centralHi := (5233657726328382611/1562500000000000000)
  directionLo := (169327678530330294347/50000000000000000000)
  directionHi := (67731071412132117739/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree047.table
  base := (-6499970784119052094170073105056214774957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-99861307943474138204809778798894586000000000000)
      constant := (1216654332101005574050825203395400524506260782389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree047.table
  base := (-6500004279508175391874110892674138710353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1586799670625867172868142181295922000000000000)
      constant := (19354027803304011321408138044097888670476374087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169327678530330294347/50000000000000000000)
  centralHi := (67731071412132117739/20000000000000000000)
  directionLo := (342316602459608550941/100000000000000000000)
  directionHi := (171158301229804275471/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree048.table
  base := (-3138386020125721772125652281981629281539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-11331460254634116583115016956917254000000000000)
      constant := (141146134527384819003501342193933854358592430534) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree048.table
  base := (-6276799053893872377816396205153480512317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1620515741437384333529228215693322000000000000)
      constant := (20207595480355057073693466284975417894111134843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342316602459608550941/100000000000000000000)
  centralHi := (171158301229804275471/50000000000000000000)
  directionLo := (345939101249187849611/100000000000000000000)
  directionHi := (86484775312296962403/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree049.table
  base := (-3010409681322100737739633345602384993713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-14872139519991422898751503775087998000000000000)
      constant := (189311855268256165479980952143510773918508263486) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree049.table
  base := (-3010420569688758855026535528853648254931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1654231812248901494190314250090722000000000000)
      constant := (21080358230200836209043851155196691452084433898) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345939101249187849611/100000000000000000000)
  centralHi := (86484775312296962403/25000000000000000000)
  directionLo := (349524058151512663217/100000000000000000000)
  directionHi := (174762029075756331609/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree050.table
  base := (-5732136062835002008819203594518895935557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-106226810988172871334485900238976686000000000000)
      constant := (1381257595110257896685254860298914276745343208589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree050.table
  base := (-2866076805291785511154490872739845059339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1687947883060418654851400284488122000000000000)
      constant := (21972315025535993160106228772855598716226336762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349524058151512663217/100000000000000000000)
  centralHi := (174762029075756331609/50000000000000000000)
  directionLo := (11033519272623918631/3125000000000000000)
  directionHi := (353072616723965396193/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree051.table
  base := (-5410740551646384292996071735899083838837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1719819767244536228217639270672022000000000000)
      constant := (22833952123885064750554483921743228888411137923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree051.table
  base := (-43286037488096717228096141849120391063/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1721663953871935815512486318885522000000000000)
      constant := (22883465055254686874094190571184635883685522125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11033519272623918631/3125000000000000000)
  centralHi := (353072616723965396193/100000000000000000000)
  directionLo := (44573232952551371403/12500000000000000000)
  directionHi := (14263434544816438849/4000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree052.table
  base := (-158020230292580373270983785627743086431/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-110470479684638693420936647865698086000000000000)
      constant := (1497027112178373089221743878302874668098794985184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree052.table
  base := (-1264164687484643085655110176566777311751/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1755380024683452976173572353282922000000000000)
      constant := (23813807678954587871650575781413026029214134916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44573232952551371403/12500000000000000000)
  centralHi := (14263434544816438849/4000000000000000000)
  directionLo := (360064832478153156203/100000000000000000000)
  directionHi := (90016208119538289051/25000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree053.table
  base := (-4669867999358521785913984043681552344771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-112592314032871604464162021679058786000000000000)
      constant := (1556721948022265729977144251108160515307682369467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree053.table
  base := (-4669877159275223803467078259662906986831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1789096095494970136834658387680322000000000000)
      constant := (24763342391014607886710833086459713718039297049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360064832478153156203/100000000000000000000)
  centralHi := (90016208119538289051/25000000000000000000)
  directionLo := (90877626867510224439/25000000000000000000)
  directionHi := (363510507470040897757/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree054.table
  base := (-4250411510700122700547539876925041657113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-12746016486789390611931932832491054000000000000)
      constant := (179735940655479156432704426236073767542685704889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree054.table
  base := (-531302360080482586204721689031103464583/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1822812166306487297495744422077722000000000000)
      constant := (25732068792231777020040667164738157941226402056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90877626867510224439/25000000000000000000)
  centralHi := (363510507470040897757/100000000000000000000)
  directionLo := (366923826556320573201/100000000000000000000)
  directionHi := (183461913278160286601/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree055.table
  base := (-759657013133260382977114698978062089269/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-116835982729337426550612769305780186000000000000)
      constant := (1679731645720588455473640534110107054782951278065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree055.table
  base := (-3798290993388783135734074983368728742549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1856528237118004458156830456475122000000000000)
      constant := (26719986567426607685347482474618650827652975971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366923826556320573201/100000000000000000000)
  centralHi := (183461913278160286601/50000000000000000000)
  directionLo := (92576421116670883277/25000000000000000000)
  directionHi := (370305684466683533109/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree056.table
  base := (-1656747160293437059176403198213763524711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-16993973868224333941976877588448698000000000000)
      constant := (249006638803012844698344289919417218614094148242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree056.table
  base := (-331349908673970644774048768190946962873/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1890244307929521618817916490872522000000000000)
      constant := (27727095467761003727493542868600540502659311670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92576421116670883277/25000000000000000000)
  centralHi := (370305684466683533109/100000000000000000000)
  directionLo := (373656935439374856359/100000000000000000000)
  directionHi := (9341423385984371409/2500000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree057.table
  base := (-2796043742421524163480842735660794599371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-13453294602867027626340390770277954000000000000)
      constant := (200840881230198390665724007838191278345489825963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree057.table
  base := (-699011893349664674613949663124787910989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1923960378741038779479002525269922000000000000)
      constant := (28753395296777058154649773548669939269659434924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373656935439374856359/100000000000000000000)
  centralHi := (9341423385984371409/2500000000000000000)
  directionLo := (188489197870561877501/50000000000000000000)
  directionHi := (376978395741123755003/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree058.table
  base := (-56148421469786160416161499114293612271/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-17600212253433737097184127249408898000000000000)
      constant := (267613716311188886219524949338615786271709811240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree058.table
  base := (-1122969968568848833337080439628210035163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1957676449552555940140088559667322000000000000)
      constant := (29798885899373755182446480029820900922049016154) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188489197870561877501/50000000000000000000)
  centralHi := (376978395741123755003/100000000000000000000)
  directionLo := (380270845988957555067/100000000000000000000)
  directionHi := (95067711497239388767/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree059.table
  base := (-1663176455452159281246616435503539419909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-125323320122269070723514264559222986000000000000)
      constant := (1940230713127148825129114686998993320053632578893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree059.table
  base := (-415794732073383136340882661245310441699/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-1991392520364073100801174594064722000000000000)
      constant := (30863567153103354180903535930386888135300475284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380270845988957555067/100000000000000000000)
  centralHi := (95067711497239388767/25000000000000000000)
  directionLo := (191767516646305116373/50000000000000000000)
  directionHi := (383535033292610232747/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree060.table
  base := (-261941183063897779183607493410771702571/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-14160572718944664640748848708064854000000000000)
      constant := (223152446860896677279098869236886192924835422252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree060.table
  base := (-261941679530777787864334317081921091559/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2025108591175590261462260628462122000000000000)
      constant := (31947438961299324576263248043672103164330807044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191767516646305116373/50000000000000000000)
  centralHi := (383535033292610232747/100000000000000000000)
  directionLo := (386771673234183223081/100000000000000000000)
  directionHi := (193385836617091611541/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree061.table
  base := (-79940685265438755681022154143028223297/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-129566988818734892809965012185944386000000000000)
      constant := (2077719935168756593435875376433673751748237192845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree061.table
  base := (-4996312758463540544633840110440466761/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2058824661987107422123346662859522000000000000)
      constant := (33050501247650417390622312324571388398346681520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386771673234183223081/100000000000000000000)
  centralHi := (193385836617091611541/50000000000000000000)
  directionLo := (12186920365622457151/3125000000000000000)
  directionHi := (389981451699918628833/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree062.table
  base := (281006090650339540728667668643881620263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-131688823166967803853190385999305086000000000000)
      constant := (2148274449541881152331365960966792539977790928449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree062.table
  base := (281004810973611349808739082459052068631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2092540732798624582784432697256922000000000000)
      constant := (34172753951916561311876631422984123457147520751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12186920365622457151/3125000000000000000)
  centralHi := (389981451699918628833/100000000000000000000)
  directionLo := (98291256644341886811/25000000000000000000)
  directionHi := (78633005315473509449/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree063.table
  base := (994362735603806673314779076225358430669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2123978690717471665022472377978822000000000000)
      constant := (35238659711581192763106706093259625182691814549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree063.table
  base := (124295213595139341510138769404549403797/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2126256803610141743445518731654322000000000000)
      constant := (35314197026546307238611681571650665552051569896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98291256644341886811/25000000000000000000)
  centralHi := (78633005315473509449/20000000000000000000)
  directionLo := (396323029329848927421/100000000000000000000)
  directionHi := (198161514664924463711/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree064.table
  base := (43509141334696482125991684000833100161/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-135932491863433625939641133626026486000000000000)
      constant := (2293003269633427227317850593820744891939715060120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree064.table
  base := (1740364829632736136201043533546456208399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2159972874421658904106604766051722000000000000)
      constant := (36474830434006106325187836187779229776854131879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396323029329848927421/100000000000000000000)
  centralHi := (198161514664924463711/50000000000000000000)
  directionLo := (79891213291774323021/20000000000000000000)
  directionHi := (199728033229435807553/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree065.table
  base := (2519014168859804206754927469817779279241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-19722046601666648140409501062769598000000000000)
      constant := (338168224437094521139282850557814386161619797049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree065.table
  base := (2519013508187195110408972474498888798581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2193688945233176064767690800449122000000000000)
      constant := (37654654144671628164612307600409595028201624701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79891213291774323021/20000000000000000000)
  centralHi := (199728033229435807553/50000000000000000000)
  directionLo := (402564720864112258999/100000000000000000000)
  directionHi := (402564720864112259/100000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree066.table
  base := (416288468628666801275288266504358360799/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-15575128951099938669565764583638654000000000000)
      constant := (271395384957041659346354462822862524160543407624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree066.table
  base := (1665153609639235005796642954498201991097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2227405016044693225428776834846522000000000000)
      constant := (38853668135162846727312123773134480901691259074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402564720864112258999/100000000000000000000)
  centralHi := (402564720864112259/100000000000000000)
  directionLo := (202824776554792969477/50000000000000000000)
  directionHi := (81129910621917187791/20000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree067.table
  base := (834849194633069146519552290578394670043/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-142297994908132359069317255066108586000000000000)
      constant := (2519145949114490807973308803587257855368070086945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree067.table
  base := (2087122774244858930957468834448651493881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2261121086856210386089862869243922000000000000)
      constant := (40071872387029509747070912531502050826318152002) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202824776554792969477/50000000000000000000)
  centralHi := (81129910621917187791/20000000000000000000)
  directionLo := (102177775650949698919/25000000000000000000)
  directionHi := (408711102603798795677/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree068.table
  base := (5050828509187176477875674796864649477693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-144419829256365270112542628879469286000000000000)
      constant := (2596940023631581791762992011791038524741971313339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree068.table
  base := (5050828168821116878060380543440276074931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2294837157667727546750948903641322000000000000)
      constant := (41309266885713258158273771440142000531132003051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102177775650949698919/25000000000000000000)
  centralHi := (408711102603798795677/100000000000000000000)
  directionLo := (411749888700918910257/100000000000000000000)
  directionHi := (205874944350459455129/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree069.table
  base := (1192011019003841930722569036883946799487/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-16282407067177575683974222521425554000000000000)
      constant := (297326743047730240800744485575120842841098625445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree069.table
  base := (238402192891359524111986876839200682761/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2328553228479244707412034938038722000000000000)
      constant := (42565851619728177985065866224041269339930062025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411749888700918910257/100000000000000000000)
  centralHi := (205874944350459455129/50000000000000000000)
  directionLo := (414766411729331421119/100000000000000000000)
  directionHi := (1296145036654160691/312500000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree070.table
  base := (3450962761932736111363970716563209248943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-21237642564690156028427625215170098000000000000)
      constant := (393735419989776547546092615453043701501499443454) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree070.table
  base := (345096265268436106151258008782931031103/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2362269299290761868073120972436122000000000000)
      constant := (43841626580013817906766231125165037448714733260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414766411729331421119/100000000000000000000)
  centralHi := (1296145036654160691/312500000000000000)
  directionLo := (104440288488336553441/25000000000000000000)
  directionHi := (83552230790669242753/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree071.table
  base := (984554954072523498819270801277236693581/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-150785332301064003242218750319551386000000000000)
      constant := (2837561780670577763187181915842375098836799529304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree071.table
  base := (1575287891514260540423026396654982676589/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2395985370102279028734207006833522000000000000)
      constant := (45136591759424378616504230844606544418722094345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104440288488336553441/25000000000000000000)
  centralHi := (83552230790669242753/20000000000000000000)
  directionLo := (420734580473292687291/100000000000000000000)
  directionHi := (105183645118323171823/25000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree072.table
  base := (111044966156043257821080156924079438549/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2427097883322173242626097208458922000000000000)
      constant := (46352098560239263895751754367977379254691202320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree072.table
  base := (555224822020922865998887293847869077053/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2429701440913796189395293041230922000000000000)
      constant := (46450747152325417520744310663581599666871625808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420734580473292687291/100000000000000000000)
  centralHi := (105183645118323171823/25000000000000000000)
  directionLo := (423687140068758475431/100000000000000000000)
  directionHi := (52960892508594809429/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree073.table
  base := (4961699201054035831001656936684909640311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-155029000997529825328669497946272786000000000000)
      constant := (3004009225517325831458382208069261714624132039906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree073.table
  base := (9923398289897381061199094654728820183863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2463417511725313350056379075628322000000000000)
      constant := (47784092754275442614852965554063787803405764623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423687140068758475431/100000000000000000000)
  centralHi := (52960892508594809429/12500000000000000000)
  directionLo := (426619265989300964903/100000000000000000000)
  directionHi := (53327408248662620613/12500000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree074.table
  base := (10995842881471428951986459030007715984497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-157150835345762736371894871759633486000000000000)
      constant := (3089042829112997367210267931456636185970784829031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree074.table
  base := (1099584279164628705971452751382816676863/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2497133582536830510717465110025722000000000000)
      constant := (49136628561774530702760493663150571812706176230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426619265989300964903/100000000000000000000)
  centralHi := (53327408248662620613/12500000000000000000)
  directionLo := (214765688348288127093/50000000000000000000)
  directionHi := (429531376696576254187/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree075.table
  base := (12100930667552038895524910964723585405543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-17696963299332849712791138396999354000000000000)
      constant := (352809224433924899771563748503304011220881259321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree075.table
  base := (2420186119131951166957761103882099203411/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2530849653348347671378551144423122000000000000)
      constant := (50508354572065864531433627263061324693175305655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214765688348288127093/50000000000000000000)
  centralHi := (429531376696576254187/100000000000000000000)
  directionLo := (216211938280742406007/50000000000000000000)
  directionHi := (86484775312296962403/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree076.table
  base := (1654832713839659393548265673823575651491/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-161394504042228558458345619386354886000000000000)
      constant := (3262729797755095291739090265724064899436335528744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree076.table
  base := (13238661653187930407196352404156923750837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2564565724159864832039637178820522000000000000)
      constant := (51899270782979051718300264472798742402311014077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216211938280742406007/50000000000000000000)
  centralHi := (86484775312296962403/20000000000000000000)
  directionLo := (435297156519622141617/100000000000000000000)
  directionHi := (217648578259811070809/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree077.table
  base := (14409035971902448147558430046301440292131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-23359476912923067071652999028530798000000000000)
      constant := (478769023221820201260160347344666083809213678259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree077.table
  base := (7204517962937262130387846005154029103601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2598281794971381992700723213217922000000000000)
      constant := (53309377192806432031374380212343219059442840242) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435297156519622141617/100000000000000000000)
  centralHi := (217648578259811070809/50000000000000000000)
  directionLo := (438151594688042394821/100000000000000000000)
  directionHi := (219075797344021197411/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree078.table
  base := (15612053420383221788032181963781914629293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-18404241415410486727199596334786254000000000000)
      constant := (382360346023565124958123196864096624348475275571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree078.table
  base := (15612053383563534757265852823866953121233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2631997865782899153361809247615322000000000000)
      constant := (54738673800205430077197957768920096619910414393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438151594688042394821/100000000000000000000)
  centralHi := (219075797344021197411/50000000000000000000)
  directionLo := (3445215288641326117/781250000000000000)
  directionHi := (440987556946089742977/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree079.table
  base := (16847714032016628052115300728061864030781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-23965715298132470226860248689490998000000000000)
      constant := (504615664666487526737251733250133392236629608109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree079.table
  base := (8423857001283920449472398006679610607319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2665713936594416314022895282012722000000000000)
      constant := (56187160604121471541831414251713303887696898398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3445215288641326117/781250000000000000)
  centralHi := (440987556946089742977/100000000000000000000)
  directionLo := (443805397482823441271/100000000000000000000)
  directionHi := (55475674685352930159/12500000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree080.table
  base := (18116017787852155014205174851483508426957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-169881841435160202631247114639797686000000000000)
      constant := (3624582777859568264723378020774208208556622813611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree080.table
  base := (3623203552860493556055420564480557284163/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2699430007405933474683981316410122000000000000)
      constant := (57654837603727134757505407282269954454241104615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443805397482823441271/100000000000000000000)
  centralHi := (55475674685352930159/12500000000000000000)
  directionLo := (446605459313355316137/100000000000000000000)
  directionHi := (223302729656677658069/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree081.table
  base := (19416964673035095616312405965107458470517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-19111519531488123741608054272573154000000000000)
      constant := (413118054416987559255160604171703258109961211499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree081.table
  base := (3883392930841151854319845721895995922461/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2733146078217450635345067350807522000000000000)
      constant := (59141704798374120231671186189605040172319430905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446605459313355316137/100000000000000000000)
  centralHi := (223302729656677658069/50000000000000000000)
  directionLo := (449388074766230566993/100000000000000000000)
  directionHi := (224694037383115283497/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree082.table
  base := (20750554675940702718935761602501737841621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-174125510131626024717697862266519086000000000000)
      constant := (3812748788312766634733907117714101953838148938083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree082.table
  base := (2075055466088785433144237840171152858641/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2766862149028967796006153385204922000000000000)
      constant := (60647762187555339960901518752731002964195559610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449388074766230566993/100000000000000000000)
  centralHi := (224694037383115283497/50000000000000000000)
  directionLo := (226076782971906138549/50000000000000000000)
  directionHi := (452153565943812277099/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree083.table
  base := (5529196946872653845968075084565869006473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-176247344479858935760923236079879786000000000000)
      constant := (3908641673513740873473989872502903345617370477116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree083.table
  base := (11058393887729308414504785498838639935369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2800578219840484956667239419602322000000000000)
      constant := (62173009770874996194517192571579416177125126498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226076782971906138549/50000000000000000000)
  centralHi := (452153565943812277099/100000000000000000000)
  directionLo := (22745112257873754053/5000000000000000000)
  directionHi := (454902245157475081061/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree084.table
  base := (23515664000613224966551147467005758845497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2831256806795108679430930315765722000000000000)
      constant := (63583192783110732364180991863618191389560371937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree084.table
  base := (23515663990997239209642139073866825986317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2834294290652002117328325453999722000000000000)
      constant := (63717447548024967659377249118240272959736819157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22745112257873754053/5000000000000000000)
  centralHi := (454902245157475081061/100000000000000000000)
  directionLo := (45763441533927245081/10000000000000000000)
  directionHi := (457634415339272450811/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree085.table
  base := (6236795827454427067765246857810934898303/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-180491013176324757847373983706601186000000000000)
      constant := (4104047203764071643953319398593338769417051661476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree085.table
  base := (997887332085347662453423722195758824523/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2868010361463519277989411488397122000000000000)
      constant := (65281075518766175253769336512327804465664712075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45763441533927245081/10000000000000000000)
  centralHi := (457634415339272450811/100000000000000000000)
  directionLo := (92070074086322725757/20000000000000000000)
  directionHi := (230175185215806814393/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree086.table
  base := (26411345710857819634325652036617131436671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-26087549646365381270085622502851698000000000000)
      constant := (600508549826588203000613474107953039778228266319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree086.table
  base := (26411345704718465594706840348575222018657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2901726432275036438650497522794522000000000000)
      constant := (66863893682913878719141830088545409459492628297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92070074086322725757/20000000000000000000)
  centralHi := (230175185215806814393/50000000000000000000)
  directionLo := (231525197878184552361/50000000000000000000)
  directionHi := (463050395756369104723/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree087.table
  base := (27908151200466560462407415258480265263371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-20526075763643397770424970148146954000000000000)
      constant := (478253231154772235255453672597035427228533782037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree087.table
  base := (13954075597781009922550329351134933428839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2935442503086553599311583557191922000000000000)
      constant := (68465902040326076479946814696983270742370682238) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231525197878184552361/50000000000000000000)
  centralHi := (463050395756369104723/100000000000000000000)
  directionLo := (232867384182358293593/50000000000000000000)
  directionHi := (465734768364716587187/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree088.table
  base := (29437599776146814692162723781908843728671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-186856516221023490977050105146683286000000000000)
      constant := (4406204898577565764270111111806855556793582180233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree088.table
  base := (1471879988611462303066087149029770819447/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-2969158573898070759972669591589322000000000000)
      constant := (70087100590894355081732824157709024533051997740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232867384182358293593/50000000000000000000)
  centralHi := (465734768364716587187/100000000000000000000)
  directionLo := (46840375736894166993/10000000000000000000)
  directionHi := (468403757368941669931/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree089.table
  base := (15499845718003087012814227767234624354533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-188978350569256402020275478960043986000000000000)
      constant := (4509337303334656491597860676115711935571908625318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree089.table
  base := (3874961429109670846860094785617798684537/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3002874644709587920633755625986722000000000000)
      constant := (71727489334536672228825244791701678121874174216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46840375736894166993/10000000000000000000)
  centralHi := (468403757368941669931/100000000000000000000)
  directionLo := (471057624257317950841/100000000000000000000)
  directionHi := (235528812128658975421/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree090.table
  base := (16297213089313326509879635011605322259739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-21233353879721034784833428085933854000000000000)
      constant := (512630699406693900122001442804714237732561760266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree090.table
  base := (16297213088064056884047257246461629355179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3036590715521105081294841660384122000000000000)
      constant := (73387068271191666041904603291522416401043848518) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471057624257317950841/100000000000000000000)
  centralHi := (235528812128658975421/50000000000000000000)
  directionLo := (473696623193109436083/100000000000000000000)
  directionHi := (118424155798277359021/25000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree091.table
  base := (34221804002961949769679651235034134309887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-27603145609388889158103746655252198000000000000)
      constant := (674174553221628128731832768533799440242494312143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree091.table
  base := (17110902000483481713984515386914402184711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3070306786332622241955927694781522000000000000)
      constant := (75065837400814168915196794636607234199331036862) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473696623193109436083/100000000000000000000)
  centralHi := (118424155798277359021/25000000000000000000)
  directionLo := (95264200259732589203/20000000000000000000)
  directionHi := (14885031290583217063/3125000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree092.table
  base := (17940912454128226216295605966099117248749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-195343853613955135149951600400126086000000000000)
      constant := (4825974037005992534196556558710891980677975832854) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree092.table
  base := (35881824906663725837111907123403578153477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3104022857144139402617013729178922000000000000)
      constant := (76763796723371672063389591786366674702970949517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95264200259732589203/20000000000000000000)
  centralHi := (14885031290583217063/3125000000000000000)
  directionLo := (23946549946274464909/5000000000000000000)
  directionHi := (478930998925489298181/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree093.table
  base := (9393622223495352907841188386765067342293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3134375999399810257034555146245822000000000000)
      constant := (78316393460675380188968045588114676252584906612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree093.table
  base := (18787244446354992613458750380267480849953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3137738927955656563278099763576322000000000000)
      constant := (78480946238841540308048902918542823029841515026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23946549946274464909/5000000000000000000)
  centralHi := (478930998925489298181/100000000000000000000)
  directionLo := (240763424955584353533/50000000000000000000)
  directionHi := (481526849911168707067/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree094.table
  base := (39299795959784662112941809768056757829503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-199587522310420957236402348026847486000000000000)
      constant := (5043098125600078393046541113102195533665620092969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree094.table
  base := (39299795958769837462940875585070303043439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3171454998767173723939185797973722000000000000)
      constant := (80217285947208818861205105033020782961796947719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240763424955584353533/50000000000000000000)
  centralHi := (481526849911168707067/100000000000000000000)
  directionLo := (121027195455964399863/25000000000000000000)
  directionHi := (484108781823857599453/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree095.table
  base := (20528873052725518914561632065501031502403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-201709356658653868279627721840208186000000000000)
      constant := (5153470049737977354940411291425378219363328979338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree095.table
  base := (20528873052320559366808507163190833067027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3205171069578690884600271832371122000000000000)
      constant := (81972815848464507187803511995894928157954218134) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121027195455964399863/25000000000000000000)
  centralHi := (484108781823857599453/100000000000000000000)
  directionLo := (486677016195120438357/100000000000000000000)
  directionHi := (243338508097560219179/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree096.table
  base := (42848339330871225435407243467230689037451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-22647910111876308813650343961507654000000000000)
      constant := (585005395603993248111525736623801866546454491797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree096.table
  base := (2678021208139056910310095408867240395831/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3238887140390208045261357866768522000000000000)
      constant := (83747535942604201338463864760270566554604671216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486677016195120438357/100000000000000000000)
  centralHi := (243338508097560219179/50000000000000000000)
  directionLo := (122307942185440191067/25000000000000000000)
  directionHi := (489231768741760764269/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree097.table
  base := (44671575636017275695887878689061655916673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-205953025355119690366078469466929586000000000000)
      constant := (5377833657693885634576800920216594642933170513879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree097.table
  base := (44671575635501572842253950033803034502191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3272603211201725205922443901165922000000000000)
      constant := (85541446229627026915638693628641678899072045511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122307942185440191067/25000000000000000000)
  centralHi := (489231768741760764269/100000000000000000000)
  directionLo := (49177324957728012659/10000000000000000000)
  directionHi := (491773249577280126591/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree098.table
  base := (46527455020923366998313911357803949707519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-29724979957621800201329120468612898000000000000)
      constant := (784546477358844631998239964540675300804356080591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree098.table
  base := (9305491004102384972833801315304424816217/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3306319282013242366583529935563322000000000000)
      constant := (87354546709534801235324295889124497486213985285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49177324957728012659/10000000000000000000)
  centralHi := (491773249577280126591/100000000000000000000)
  directionLo := (494301663413551554669/100000000000000000000)
  directionHi := (49430166341355155467/10000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree099.table
  base := (1936639099426828443981246609058879024561/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-23355188227953945828058801899294554000000000000)
      constant := (623002623543360820648871077581668367784184049175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree099.table
  base := (48415977485342485255447208599003300658287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3340035352824759527244615969960722000000000000)
      constant := (89186837382331376193212743895569203948607595527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494301663413551554669/100000000000000000000)
  centralHi := (49430166341355155467/10000000000000000000)
  directionLo := (496817209753255402437/100000000000000000000)
  directionHi := (248408604876627701219/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree100.table
  base := (6292142878796965613055903936977379885137/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-30331218342831203356536370129573098000000000000)
      constant := (817632638404173864135107769177418534950365275144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree100.table
  base := (50337143030113911141204046855789781917991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3373751423636276687905702004358122000000000000)
      constant := (91038318248022123565171304411858816880770877311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496817209753255402437/100000000000000000000)
  centralHi := (248408604876627701219/50000000000000000000)
  directionLo := (499320083073589518881/100000000000000000000)
  directionHi := (249660041536794759441/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree101.table
  base := (52290951655180776615487949784300970991181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-214440362748051334538979964720372386000000000000)
      constant := (5841039912329220730914056460561626548358397265963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree101.table
  base := (10458190330994391645019978942434741432713/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3407467494447793848566788038755522000000000000)
      constant := (92908989306613532540882640920589507616629077365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499320083073589518881/100000000000000000000)
  centralHi := (249660041536794759441/50000000000000000000)
  directionLo := (501810473001732499453/100000000000000000000)
  directionHi := (250905236500866249727/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree102.table
  base := (54277403360246960307846818690452798045021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-24062466344031582842467259837081454000000000000)
      constant := (662206438043412252456890264612638281152336659587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree102.table
  base := (10855480672016085297762755723159351656001/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3441183565259311009227874073152922000000000000)
      constant := (94798850558112895659331085358236731475384102605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (501810473001732499453/100000000000000000000)
  centralHi := (250905236500866249727/50000000000000000000)
  directionLo := (126072141120627008927/25000000000000000000)
  directionHi := (504288564482508035709/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree103.table
  base := (28148249072874234024946123650680198448857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-218684031444517156625430712347093786000000000000)
      constant := (6079882559014174250459399433379151160507836874622) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree103.table
  base := (56296498145615669174466319901578755722169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3474899636070828169888960107550322000000000000)
      constant := (96707902002528064343209089907252453783506686049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126072141120627008927/25000000000000000000)
  centralHi := (504288564482508035709/100000000000000000000)
  directionLo := (506754537938669897519/100000000000000000000)
  directionHi := (6334431724233373719/1250000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree104.table
  base := (58348236011868219543426995557290274075789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-220805865792750067668656086160454486000000000000)
      constant := (6201113762200125723342987138701784562404076730347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree104.table
  base := (58348236011762331867170694147351357357187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3508615706882345330550046141947722000000000000)
      constant := (98636143639867259198611478257537317780899322427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506754537938669897519/100000000000000000000)
  centralHi := (6334431724233373719/1250000000000000000)
  directionLo := (25460428471210033423/5000000000000000000)
  directionHi := (509208569424200668461/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree105.table
  base := (60432616958794480995585921831220655792589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3538534922872745693839388253552622000000000000)
      constant := (100373834157922107050010636703935184816541854869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree105.table
  base := (15108154239677514717331570170366293694111/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3542331777693862491211132176345122000000000000)
      constant := (100583575470138923379525373176168821046222063324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25460428471210033423/5000000000000000000)
  centralHi := (509208569424200668461/100000000000000000000)
  directionLo := (255825415385496420811/50000000000000000000)
  directionHi := (511650830770992841623/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree106.table
  base := (15637410246679565393330016337960794060049/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-225049534489215889755106833787175886000000000000)
      constant := (6447195928261611059787123469020083959111555265308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree106.table
  base := (62549640986650959605290389752772488406031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3576047848505379651872218210742522000000000000)
      constant := (102550197493351609789632586472736115956324906151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255825415385496420811/50000000000000000000)
  centralHi := (511650830770992841623/100000000000000000000)
  directionLo := (257040744864629058413/50000000000000000000)
  directionHi := (514081489729258116827/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree107.table
  base := (16174827023957830126934204405817206563091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-32453052691064114399761743942933798000000000000)
      constant := (938863841591174074422031362268431658722233478796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree107.table
  base := (1010926688996526119316337501985718555983/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3609763919316896812533304245139922000000000000)
      constant := (104536009709513894845794527736471949253178825152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257040744864629058413/50000000000000000000)
  centralHi := (514081489729258116827/100000000000000000000)
  directionLo := (64562588762748697629/12500000000000000000)
  directionHi := (516500710101989581033/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree108.table
  base := (66881618286324653216598953193501599243651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-25477022576186856871284175712655254000000000000)
      constant := (744233826731050092888065994613420644899486103197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree108.table
  base := (33440809143140945732502938883022977588509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3643479990128413973194390279537322000000000000)
      constant := (106541012118634313068012977545954507970436018378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64562588762748697629/12500000000000000000)
  centralHi := (516500710101989581033/100000000000000000000)
  directionLo := (518908651873781774417/100000000000000000000)
  directionHi := (259454325936890887209/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree109.table
  base := (69096571558387352679372686016292330044559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-231415037533914622884782955227257986000000000000)
      constant := (6825368576585838377240192080565777816032570108057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree109.table
  base := (69096571558353271615023187375186237316191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3677196060939931133855476313934722000000000000)
      constant := (108565204720721307976284540821838864471554139511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (518908651873781774417/100000000000000000000)
  centralHi := (259454325936890887209/50000000000000000000)
  directionLo := (521305471334295328829/100000000000000000000)
  directionHi := (52130547133429532883/10000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree110.table
  base := (17836041978051441073580641215588799072567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-233536871882147533928008329040618686000000000000)
      constant := (6953839299157903810556010489490718498724458362564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree110.table
  base := (1114752623627790687707049490302869427731/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3710912131751448294516562348332122000000000000)
      constant := (110608587515783195733989120500438959186688758464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521305471334295328829/100000000000000000000)
  centralHi := (52130547133429532883/10000000000000000000)
  directionLo := (523691321196635807101/100000000000000000000)
  directionHi := (261845660598317903551/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree111.table
  base := (14724881469592573961280113774568170692297/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-26184300692264493885692633650442154000000000000)
      constant := (787057400921795596371874513698469717458711415795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree111.table
  base := (73624407347941226705704761588161465353413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3744628202562965455177648382729522000000000000)
      constant := (112671160503828138734273347895098578598999300173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523691321196635807101/100000000000000000000)
  centralHi := (261845660598317903551/50000000000000000000)
  directionLo := (526066350710900473933/100000000000000000000)
  directionHi := (263033175355450236967/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree112.table
  base := (75937289865837849593478197275550882054541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-33968648654087622287779868095334298000000000000)
      constant := (1030628643428730088122539307718703543379551978749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree112.table
  base := (15187457973164120869023743192678153904659/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3778344273374482615838734417126922000000000000)
      constant := (114752923684864126922941626630786184449946616695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526066350710900473933/100000000000000000000)
  centralHi := (263033175355450236967/50000000000000000000)
  directionLo := (132107676443282975807/25000000000000000000)
  directionHi := (528430705773131903229/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree113.table
  base := (78282815466005783407121739190316727843529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-239902374926846267057684450480700786000000000000)
      constant := (7346490986273245626802751495472763533540270540367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree113.table
  base := (78282815465992043468064480916309033615593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3812060344185999776499820451524322000000000000)
      constant := (116853877058898965122308654251260480485599815953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132107676443282975807/25000000000000000000)
  centralHi := (528430705773131903229/100000000000000000000)
  directionLo := (530784529029903491537/100000000000000000000)
  directionHi := (265392264514951745769/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree114.table
  base := (80660984148637458190920606533291309945937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3841654115477447271443013084032722000000000000)
      constant := (118726794525603879751258395757311800410103061177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree114.table
  base := (20165246037156627980271976826909648206647/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3845776414997516937160906485921722000000000000)
      constant := (118974020625940264991870498582691685791232524348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530784529029903491537/100000000000000000000)
  centralHi := (265392264514951745769/50000000000000000000)
  directionLo := (1332819899946872571/250000000000000000)
  directionHi := (533127959978749028401/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree115.table
  base := (20767948978474814581180527539792850041871/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-244146043623312089144135198107422186000000000000)
      constant := (7614291710520973688172793939717967644131962975332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree115.table
  base := (41535897956945269186536449156195532331417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3879492485809034097821992520319122000000000000)
      constant := (121113354385995440554494539878334492589854032514) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1332819899946872571/250000000000000000)
  centralHi := (533127959978749028401/100000000000000000000)
  directionLo := (133865283766159100909/25000000000000000000)
  directionHi := (535461135064636403637/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree116.table
  base := (85515250761953118946343698602725470063153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-246267877971545000187360571920782886000000000000)
      constant := (7750001952497487617732355065946371097118942986919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree116.table
  base := (85515250761946173036100994239954507493017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3913208556620551258483078554716522000000000000)
      constant := (123271878339071706447672860394303166628096609857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133865283766159100909/25000000000000000000)
  centralHi := (535461135064636403637/100000000000000000000)
  directionLo := (26889209388633712323/5000000000000000000)
  directionHi := (537784187772674246461/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree117.table
  base := (87991348692956527182973609263099149907287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-27598856924419767914509549526015954000000000000)
      constant := (876324309004780881836055978331381958771156271689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree117.table
  base := (87991348692950994803216291271572853473027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3946924627432068419144164589113922000000000000)
      constant := (125449592485176078241302676336682869009472635067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26889209388633712323/5000000000000000000)
  centralHi := (537784187772674246461/100000000000000000000)
  directionLo := (16878039022413429197/3125000000000000000)
  directionHi := (108019449743445946861/20000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree118.table
  base := (3620003588282502376762653561233835233291/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-250511546668010822273811319547504286000000000000)
      constant := (8025042196158023996713114972158220014013624062325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree118.table
  base := (90500089707058153230529667193801463132209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-3980640698243585579805250623511322000000000000)
      constant := (127646496824315374306771600095408830940109076889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16878039022413429197/3125000000000000000)
  centralHi := (108019449743445946861/20000000000000000000)
  directionLo := (542400445727625927493/100000000000000000000)
  directionHi := (271200222863812963747/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree119.table
  base := (1453773028194061645669669169909357541231/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-36090483002320533331005241908694998000000000000)
      constant := (1166338885406127565527491700477345008085651722176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree119.table
  base := (2907546056388013635187253843906577734523/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4014356769055102740466336657908722000000000000)
      constant := (129862591356496218834981618185929489914198351456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542400445727625927493/100000000000000000000)
  centralHi := (271200222863812963747/50000000000000000000)
  directionLo := (136173475982644432771/25000000000000000000)
  directionHi := (108938780786115546217/20000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree120.table
  base := (764924007881385211177160211992525250177/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-28306135040497404928918007463802854000000000000)
      constant := (922767642899782225048027849349698594580238939875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree120.table
  base := (3824620039406814284094948701309305344443/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4048072839866619901127422692306122000000000000)
      constant := (132097876081725045689774266397305429580998670075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136173475982644432771/25000000000000000000)
  centralHi := (108938780786115546217/20000000000000000000)
  directionLo := (4375821966636135299/800000000000000000)
  directionHi := (68372218228689614047/12500000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree121.table
  base := (49111085624731239214041640248102366222587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-36696721387529936486212491569655198000000000000)
      constant := (1206664565846265530829210885073753716038724324886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree121.table
  base := (98222171249460253421509982960691207313191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4081788910678137061788508726703522000000000000)
      constant := (134352351000008102853096324457888195240790576511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4375821966636135299/800000000000000000)
  centralHi := (68372218228689614047/12500000000000000000)
  directionLo := (549252091380948470769/100000000000000000000)
  directionHi := (54925209138094847077/10000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree122.table
  base := (100861484597424168470496465600823140437147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-258998884060942466446712814800947086000000000000)
      constant := (8589601722320731164658053023041454625230339959981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree122.table
  base := (50430742298711198445352444069726842785453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4115504981489654222449594761100922000000000000)
      constant := (136626016111351457273176572364873901535302306026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549252091380948470769/100000000000000000000)
  centralHi := (54925209138094847077/10000000000000000000)
  directionLo := (68939632258496628493/12500000000000000000)
  directionHi := (110303411613594605589/20000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree123.table
  base := (103533441029190518001929175245631118427719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-29013413156575041943326465401589754000000000000)
      constant := (970417563365447604466224131767615313164643343193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree123.table
  base := (103533441029189107541325026619233637907183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4149221052301171383110680795498322000000000000)
      constant := (138918871415760999970131482229711606793265694343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68939632258496628493/12500000000000000000)
  centralHi := (110303411613594605589/20000000000000000000)
  directionLo := (276886380485551372749/50000000000000000000)
  directionHi := (553772760971102745499/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree124.table
  base := (106238040544889994657936027244918700600783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-263242552757408288533163562427668486000000000000)
      constant := (8879121004829110871397327893919256008575189976409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree124.table
  base := (53119020272444435890063848248099754618041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4182937123112688543771766829895722000000000000)
      constant := (141230916913242451287276295720940826350699606722) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276886380485551372749/50000000000000000000)
  centralHi := (553772760971102745499/100000000000000000000)
  directionLo := (11120386256729831047/2000000000000000000)
  directionHi := (556019312836491552351/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree125.table
  base := (108975283144647355572909113205660312142563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-265364387105641199576388936241029186000000000000)
      constant := (9025690525941328379941942176630958023684639981349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree125.table
  base := (108975283144646461699960201447322647698107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4216653193924205704432852864293122000000000000)
      constant := (143562152603801366202956667645564001598167421747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11120386256729831047/2000000000000000000)
  centralHi := (556019312836491552351/100000000000000000000)
  directionLo := (139564206035423536293/25000000000000000000)
  directionHi := (558256824141694145173/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree126.table
  base := (11174516882858376582990007102322692710373/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4245813038950382708247846191339522000000000000)
      constant := (145610581486127314483200002828575428021585163330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree126.table
  base := (111745168828583054303043150471061765984833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4250369264735722865093938898690522000000000000)
      constant := (145912578487443139638488461736801512883410749993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139564206035423536293/25000000000000000000)
  centralHi := (558256824141694145173/100000000000000000000)
  directionLo := (560485403159062284539/100000000000000000000)
  directionHi := (28024270157953114227/5000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree127.table
  base := (114547697596816915897518437454101369078173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-269608055802107021662839683867750586000000000000)
      constant := (9322449327883518269829538705341066256321948428379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree127.table
  base := (114547697596816349554635887361298599567781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4284085335547240025755024933087922000000000000)
      constant := (148282194564173011714024989239700768951357177901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560485403159062284539/100000000000000000000)
  centralHi := (28024270157953114227/5000000000000000000)
  directionLo := (56270515601688132187/10000000000000000000)
  directionHi := (562705156016881321871/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree128.table
  base := (14672858681182642153039661653592251489501/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-38818555735762847529437865383015898000000000000)
      constant := (1353234086959163061654611822229576589256613329512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree128.table
  base := (29345717362365171617298325611671488009903/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4317801406358757186416110967485322000000000000)
      constant := (150671000833996072916828796326583721270755565852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56270515601688132187/10000000000000000000)
  centralHi := (562705156016881321871/100000000000000000000)
  directionLo := (141229046689586158477/25000000000000000000)
  directionHi := (564916186758344633909/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree129.table
  base := (120250684386627515388643858515546607857189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-30427969388730315972143381277163554000000000000)
      constant := (1069337164013133541453883212679175679698869380283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree129.table
  base := (6012534219331357832614382335193712895063/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4351517477170274347077197001882722000000000000)
      constant := (153078997296917269156271565183181823836021996460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141229046689586158477/25000000000000000000)
  centralHi := (564916186758344633909/100000000000000000000)
  directionLo := (2268474389593834763/400000000000000000)
  directionHi := (567118597398458690751/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree130.table
  base := (12315114240842400037856779700661182604249/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-275973558846805754792515805307832686000000000000)
      constant := (9776636930096002374946924699183525231755974929270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree130.table
  base := (61575571204211857446546346511081191053903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4385233547981791507738283036280122000000000000)
      constant := (155506183952941406687522101352299551413821630926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2268474389593834763/400000000000000000)
  centralHi := (567118597398458690751/100000000000000000000)
  directionLo := (71164060997370852493/12500000000000000000)
  directionHi := (113862497595793363989/20000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree131.table
  base := (3940132609842359803534736605237329129187/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-278095393195038665835741179121193386000000000000)
      constant := (9930445970647837223457959251621155374403637404832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree131.table
  base := (126084243514955286534758895839291123278429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4418949618793308668399369070677522000000000000)
      constant := (157952560802073156891782806215959562099478937509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71164060997370852493/12500000000000000000)
  centralHi := (113862497595793363989/20000000000000000000)
  directionLo := (285748978310687667123/50000000000000000000)
  directionHi := (571497956621375334247/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree132.table
  base := (25809997541264810444239155979763400841823/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-31135247504807952986551839214950454000000000000)
      constant := (1120606844197110277963304014523552930910758062405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree132.table
  base := (129049987706323871451939984787964513840631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4452665689604825829060455105074922000000000000)
      constant := (160418127844317060905473138471139472120698732751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285748978310687667123/50000000000000000000)
  centralHi := (571497956621375334247/100000000000000000000)
  directionLo := (573675099578161546887/100000000000000000000)
  directionHi := (71709387447270193361/12500000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree133.table
  base := (66024187491314394187628634090140311221193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-40334151698786355417455989535416398000000000000)
      constant := (1463097687353535195830559009569460636325817203954) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree133.table
  base := (132048374982628644542677066488955164543009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4486381760416342989721541139472322000000000000)
      constant := (162902885079677534094228786225702698880619303689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (573675099578161546887/100000000000000000000)
  centralHi := (71709387447270193361/12500000000000000000)
  directionLo := (143961002820559822349/25000000000000000000)
  directionHi := (575844011282239289397/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree134.table
  base := (135079405343966167137740817956259022406371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-284460896239737398965417300561275486000000000000)
      constant := (10399112611750369341939389320510218414002904727333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree134.table
  base := (8442462833997878293813445518641639598319/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4520097831227860150382627173869722000000000000)
      constant := (165406832508158870370219526361725858984908163184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143961002820559822349/25000000000000000000)
  centralHi := (575844011282239289397/100000000000000000000)
  directionLo := (578004784394753858337/100000000000000000000)
  directionHi := (289002392197376929169/50000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree135.table
  base := (34535769697607499831203482800379919069067/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4548932231555084285851471021819622000000000000)
      constant := (167583301565097214885412702740878277507495727628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree135.table
  base := (69071539395214954140610262521981562892463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4553813902039377311043713208267122000000000000)
      constant := (167929970129765246353269651262509252323070690446) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (578004784394753858337/100000000000000000000)
  centralHi := (289002392197376929169/50000000000000000000)
  directionLo := (290078754925637417311/50000000000000000000)
  directionHi := (580157509851274834623/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree136.table
  base := (141239395322111551526021283737419202520043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-288704564936203221051868048187996886000000000000)
      constant := (10717589972027267944968232389752848595869874567389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree136.table
  base := (7061969766105573954875732648333469601541/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4587529972850894471704799242664522000000000000)
      constant := (170472297944500725377736111710081680002604137220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290078754925637417311/50000000000000000000)
  centralHi := (580157509851274834623/100000000000000000000)
  directionLo := (18196946153326622799/3125000000000000000)
  directionHi := (582302276906451929569/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree137.table
  base := (2255755545923431760059177284474211155763/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-290826399284436132095093422001357586000000000000)
      constant := (10878638532029048656753210582763375364818601276736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree137.table
  base := (72184177469549787513688782760283679209679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4621246043662411632365885277061922000000000000)
      constant := (173033815952369261348174197164276793364188237518) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18196946153326622799/3125000000000000000)
  centralHi := (582302276906451929569/100000000000000000000)
  directionLo := (146109793294298975857/25000000000000000000)
  directionHi := (584439173177195903429/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree138.table
  base := (73764978820740338567371079456152305196687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-32549803736963227015368755090524254000000000000)
      constant := (1226765964289634345165320365693609016915263826978) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree138.table
  base := (73764978820740315651850766988495986800659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4654962114473928793026971311459322000000000000)
      constant := (175614524153374702447587504434365695656704278678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146109793294298975857/25000000000000000000)
  centralHi := (584439173177195903429/100000000000000000000)
  directionLo := (117313656936888732713/20000000000000000000)
  directionHi := (293284142342221831783/50000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree139.table
  base := (4710131357166838282731150045790426403059/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-295070067980901954181544169628078986000000000000)
      constant := (11204355411760485292115535507035150660963428913824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree139.table
  base := (150724203429338788592955945593092448860533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4688678185285445953688057345856722000000000000)
      constant := (178214422547520794702587917110423926915719789693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117313656936888732713/20000000000000000000)
  centralHi := (293284142342221831783/50000000000000000000)
  directionLo := (588689695893563870281/100000000000000000000)
  directionHi := (294344847946781935141/50000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree140.table
  base := (9621943268922249934937251547027190672691/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-42455986047019266460681363348777098000000000000)
      constant := (1624146247355800998852148940579834868055198145584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree140.table
  base := (76975546151377984982145698361939728572111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4722394256096963114349143380254122000000000000)
      constant := (180833511134811185410137088892772917311517907662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (588689695893563870281/100000000000000000000)
  centralHi := (294344847946781935141/50000000000000000000)
  directionLo := (590803489753456748909/100000000000000000000)
  directionHi := (59080348975345674891/10000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree141.table
  base := (3930265606545299447985430943156607948863/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-33257081853040864029777213028311154000000000000)
      constant := (1281655404199699774683379869569337649897572294440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree141.table
  base := (157210624261811954859126366259502059759743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4756110326908480275010229414651522000000000000)
      constant := (183471789915249426430746411880080993202563518103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (590803489753456748909/100000000000000000000)
  centralHi := (59080348975345674891/10000000000000000000)
  directionLo := (296454873867199658949/50000000000000000000)
  directionHi := (592909747734399317899/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree142.table
  base := (160502799306584468512544024693236524136419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-43062224432228669615888613009737298000000000000)
      constant := (1671711447240110883697913191402274175619697592691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree142.table
  base := (16050279930658445017297900701149421595479/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4789826397719997435671315449048922000000000000)
      constant := (186129258888838977353111249753670457988523205590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (296454873867199658949/50000000000000000000)
  centralHi := (592909747734399317899/100000000000000000000)
  directionLo := (595008549864684885997/100000000000000000000)
  directionHi := (297504274932342442999/50000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree143.table
  base := (163827617437149173146225720490191011624731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-303557405373833598354445664881521786000000000000)
      constant := (11870268210141253965024654320019553451798312877613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree143.table
  base := (163827617437149158561719003003608076723887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4823542468531514596332401483446322000000000000)
      constant := (188805918055583208535173576715962781183824173127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (595008549864684885997/100000000000000000000)
  centralHi := (297504274932342442999/50000000000000000000)
  directionLo := (597099974766103439207/100000000000000000000)
  directionHi := (74637496845762929901/12500000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree144.table
  base := (83592539326789927840608092076570062490057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-33964359969118501044185670966098054000000000000)
      constant := (1337751430686548689349046220877545196529677587758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree144.table
  base := (83592539326789922041740028274182552445797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4857258539343031756993487517843722000000000000)
      constant := (191501767415485404026565563327613730834878656474) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (597099974766103439207/100000000000000000000)
  centralHi := (74637496845762929901/12500000000000000000)
  directionLo := (599184099688307422657/100000000000000000000)
  directionHi := (299592049844153711329/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree145.table
  base := (85287591477974202253866884522324933294309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-307801074070299420440896412508243186000000000000)
      constant := (12210464128794030537445994755984431642754687304614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree145.table
  base := (34115036591189679057110049278437630450267/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4890974610154548917654573552241122000000000000)
      constant := (194216806968548764377301022142492798726381685535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599184099688307422657/100000000000000000000)
  centralHi := (299592049844153711329/50000000000000000000)
  directionLo := (601261000542105417051/100000000000000000000)
  directionHi := (150315250135526354263/25000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree146.table
  base := (86998965172162446587893593102161336264317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-309922908418532331484121786321603886000000000000)
      constant := (12382371967986727508843146707203358897329780801782) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree146.table
  base := (173997930344324885842922957568524461613951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4924690680966066078315659586638522000000000000)
      constant := (196951036714776409337464333655674089555514712471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601261000542105417051/100000000000000000000)
  centralHi := (150315250135526354263/25000000000000000000)
  directionLo := (60333075193172430733/10000000000000000000)
  directionHi := (603330751931724307331/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree147.table
  base := (44363330204694409670597578722337948319681/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4953091155028019722656304129126422000000000000)
      constant := (199293434821543186276466465101817255188562071204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree147.table
  base := (177453320818777632852060060774560361756249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4958406751777583238976745621035922000000000000)
      constant := (199704456654171380452507076812467035865749961729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60333075193172430733/10000000000000000000)
  centralHi := (603330751931724307331/100000000000000000000)
  directionLo := (605393427186078736819/100000000000000000000)
  directionHi := (30269671359303936841/5000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree148.table
  base := (36188270875874651503082803963256674844583/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-314166577114998153570572533948325286000000000000)
      constant := (12729807406105697064626075961004673290538039119045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree148.table
  base := (180941354379373252879956855939956954286867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-4992122822589100399637831655433322000000000000)
      constant := (202477066786736643558608449361040079561805605707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605393427186078736819/100000000000000000000)
  centralHi := (30269671359303936841/5000000000000000000)
  directionLo := (607449098389084927587/100000000000000000000)
  directionHi := (151862274597271231897/25000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree149.table
  base := (36892406205235343910045173514895867378079/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-45184058780461580659113986823097998000000000000)
      constant := (1843619286433191246495707252885398773019275482155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree149.table
  base := (184462031026176715864931665642706936865697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-5025838893400617560298917689830722000000000000)
      constant := (205268867112475091182392321340888033536197696137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (607449098389084927587/100000000000000000000)
  centralHi := (151862274597271231897/25000000000000000000)
  directionLo := (15237445910226358047/2500000000000000000)
  directionHi := (609497836409054321881/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree150.table
  base := (188015350759251399891549230317267023409649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-35378916201273775073002586841671854000000000000)
      constant := (1453563243393035941544485250205228166044546881903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree150.table
  base := (37603070151850279392357642421844162899429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-5059554964212134720960003724228122000000000000)
      constant := (208079857631389544849125709269252919882227392545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15237445910226358047/2500000000000000000)
  centralHi := (609497836409054321881/100000000000000000000)
  directionLo := (76442463865900119417/12500000000000000000)
  directionHi := (611539710927200955337/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree151.table
  base := (191601313578659128749207219075483932972629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-320532080159696886700248655388407386000000000000)
      constant := (13260009962620824732711932093703306267332088189667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree151.table
  base := (766405254314636505680755072638307411079/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-5093271035023651881621089758625522000000000000)
      constant := (210910038343482757303353827194357443062162039750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76442463865900119417/12500000000000000000)
  centralHi := (611539710927200955337/100000000000000000000)
  directionLo := (613574790465295005603/100000000000000000000)
  directionHi := (153393697616323751401/25000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree152.table
  base := (195219919484460239432660751135090595362081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-322653914507929797743474029201768086000000000000)
      constant := (13439157321283011726158687394171309400955258116663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree152.table
  base := (19521991948446023758128480297121871924041/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-5126987105835169042282175793022922000000000000)
      constant := (213759409248757414645758079675450572599302293610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (613574790465295005603/100000000000000000000)
  centralHi := (153393697616323751401/25000000000000000000)
  directionLo := (123120628482498713129/20000000000000000000)
  directionHi := (307801571206246782823/50000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree153.table
  base := (99435584238356807272772782281652092090609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-36086194317351412087411044779458754000000000000)
      constant := (1513279029613783289946845617222663241087524046046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree153.table
  base := (49717792119178403268479841445864080510933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-5160703176646686202943261827420322000000000000)
      constant := (216627970347216138389857188107715624913708992372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123120628482498713129/20000000000000000000)
  centralHi := (307801571206246782823/50000000000000000000)
  directionLo := (308812416525689182693/50000000000000000000)
  directionHi := (617624833051378365387/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree154.table
  base := (1582461410589661956701487489920872922807/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-46699654743485088547132110975498498000000000000)
      constant := (1971581685477728513406433458955780157272526594944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree154.table
  base := (50638765138869182322017640919008668288941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-5194419247458203363604347861817722000000000000)
      constant := (219515721638861487442009367796449927683567769044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308812416525689182693/50000000000000000000)
  centralHi := (617624833051378365387/100000000000000000000)
  directionLo := (61963992758322890459/10000000000000000000)
  directionHi := (619639927583228904591/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree155.table
  base := (206271595720805700129379216432053500615193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-329019417552628530873150150641850186000000000000)
      constant := (13983838916743319066049719465883974475756007475839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree155.table
  base := (41254319144161139839933678077485454920069/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-5228135318269720524265433896215122000000000000)
      constant := (222422663123695960008015997992884059692481959745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61963992758322890459/10000000000000000000)
  centralHi := (619639927583228904591/100000000000000000000)
  directionLo := (1554121225381395651/250000000000000000)
  directionHi := (621648490152558260401/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree156.table
  base := (210020773972755314356418749571669872147897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-5256210347632721300259928959606522000000000000)
      constant := (224885914630505741343186901373163166377896522337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree156.table
  base := (210020773972755313617501427283143161438669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-5261851389081237684926519930612522000000000000)
      constant := (225348794801721995429475155127991848690410982549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1554121225381395651/250000000000000000)
  centralHi := (621648490152558260401/100000000000000000000)
  directionLo := (124730116774187538293/20000000000000000000)
  directionHi := (311825291935468845733/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree157.table
  base := (26725324413922385188362255540453260334963/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-333263086249094352959600898268571586000000000000)
      constant := (14352992913279877591059428315081908802099935412392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree157.table
  base := (213802595311379080919644070560602714600599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-5295567459892754845587605965009922000000000000)
      constant := (228294116672941975952887089394878647456733268079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124730116774187538293/20000000000000000000)
  centralHi := (311825291935468845733/50000000000000000000)
  directionLo := (625646270840135073861/100000000000000000000)
  directionHi := (312823135420067536931/50000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree158.table
  base := (217617059736729265810384319554638809712369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-335384920597327264002826272081932286000000000000)
      constant := (14539379791417513317278847467125263308173875955687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree158.table
  base := (13601066233545579083980225429737402053191/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-5329283530704272006248691999407322000000000000)
      constant := (231258628737358228434373424382755898028961864176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (625646270840135073861/100000000000000000000)
  centralHi := (312823135420067536931/50000000000000000000)
  directionLo := (62763561217459116913/10000000000000000000)
  directionHi := (627635612174591169131/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree159.table
  base := (110732083624428462131445769316379161275493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-37500750549506686116227960655032554000000000000)
      constant := (1636330361792768009901751457268356428948047133942) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree159.table
  base := (55366041812214230973002851469045972912941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-5362999601515789166909778033804722000000000000)
      constant := (234242330994973025982737626259697881040228185044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62763561217459116913/10000000000000000000)
  centralHi := (627635612174591169131/100000000000000000000)
  directionLo := (31480933401162836947/5000000000000000000)
  directionHi := (629618668023256738941/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree160.table
  base := (225343917847811942205284595501399796773603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-339628589293793086089277019708653686000000000000)
      constant := (14915773307432213826121595954376794042185927487269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree160.table
  base := (225343917847811941910563312362142258977979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-5396715672327306327570864068202122000000000000)
      constant := (237245223445788589543466104772062455511958603059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31480933401162836947/5000000000000000000)
  centralHi := (629618668023256738941/100000000000000000000)
  directionLo := (157898874397703145361/25000000000000000000)
  directionHi := (126319099518162516289/20000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree161.table
  base := (229256311533643067630841217164760102048543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-48821489091717999590357484788859198000000000000)
      constant := (2157968563615650751112727885442730618529728646127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree161.table
  base := (45851262306728613479329799061588385533493/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-5430431743138823488231950102599522000000000000)
      constant := (240267306089807089426147083692253024561683209265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157898874397703145361/25000000000000000000)
  centralHi := (126319099518162516289/20000000000000000000)
  directionLo := (158391539789573417251/25000000000000000000)
  directionHi := (126713231831658733801/20000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree162.table
  base := (58300337076599486068745665029522207807443/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-38208028665584323130636418592819454000000000000)
      constant := (1699665907751896668484797366832104907986264754484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree162.table
  base := (233201348306397944088895382413435217951593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-5464147813950340648893036136996922000000000000)
      constant := (243308578927030646777667972468394713338422871953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158391539789573417251/25000000000000000000)
  centralHi := (126713231831658733801/20000000000000000000)
  directionLo := (317765355051568856573/50000000000000000000)
  directionHi := (635530710103137713147/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree163.table
  base := (237179028166123143537699265823437744802187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (58500594)
      previous := (29250297)
      next := (29250297)
      square := (288409092212031928357668375318300000000000000)
      linear := (-49427727476927402745564734449819398000000000000)
      constant := (2212773282972126960911096339150985710527043506843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree163.table
  base := (118589514083061571694920713746415917320997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-5497863884761857809554122171394322000000000000)
      constant := (246369041957461335003441207863249952110096214874) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317765355051568856573/50000000000000000000)
  centralHi := (635530710103137713147/100000000000000000000)
  directionLo := (637489206918677668307/100000000000000000000)
  directionHi := (159372301729669417077/25000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree164.table
  base := (241189351112864195286833575299768146309357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-348115926686724730262178514962096486000000000000)
      constant := (15683039378423139091053101135231407835435849628811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree164.table
  base := (1929514808902913561354846474294577724861/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-5531579955573374970215208205791722000000000000)
      constant := (249448695181101181138803213323033019861067072625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637489206918677668307/100000000000000000000)
  centralHi := (159372301729669417077/25000000000000000000)
  directionLo := (639441705233096909007/100000000000000000000)
  directionHi := (39965106577068556813/6250000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree165.table
  base := (245232317146665617588137272537556423276853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3116470000000000000000000000000000000000000000
      center := (45500462)
      previous := (22750231)
      next := (22750231)
      square := (224318182831580388722630958580900000000000000)
      linear := (-38915306781661960145044876530606354000000000000)
      constant := (1764208040291327330631576935617520856644961406891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree165.table
  base := (245232317146665617494800912209621860405589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-5565296026384892130876294240189122000000000000)
      constant := (252547538597952167172631029564249204847117227869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (639441705233096909007/100000000000000000000)
  centralHi := (39965106577068556813/6250000000000000000)
  directionLo := (641388259827865073691/100000000000000000000)
  directionHi := (160347064956966268423/25000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree166.table
  base := (249307926267570945405883789330224329518447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-352359595383190552348629262588817886000000000000)
      constant := (16073911933401431488140046529818860180592919069881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree166.table
  base := (249307926267570945331730555692074830952739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-5599012097196409291537380274586522000000000000)
      constant := (255665572208016231325126078181779115548846893019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (641388259827865073691/100000000000000000000)
  centralHi := (160347064956966268423/25000000000000000000)
  directionLo := (643328924655671860669/100000000000000000000)
  directionHi := (64332892465567186067/10000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree167.table
  base := (63354044618905689578947738001035777641993/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-354481429731423463391854636402178586000000000000)
      constant := (16271158090761715056593967063805136823812590928956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree167.table
  base := (253416178475622758256880335277264462448967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-5632728168007926452198466308983922000000000000)
      constant := (258802796011295269281624204624796365132690459807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (643328924655671860669/100000000000000000000)
  centralHi := (64332892465567186067/10000000000000000000)
  directionLo := (322631876428937692877/50000000000000000000)
  directionHi := (129052750571575077151/20000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree168.table
  base := (64389268442715676817520635128199579401783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-5660369271105656737064762066913322000000000000)
      constant := (261422394201633547691979733042491949898187123772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree168.table
  base := (25755707377086270722328301231748805906661/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-5666444238819443612859552343381322000000000000)
      constant := (261959210007791135384205380461466581877704543810) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell127.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322631876428937692877/50000000000000000000)
  centralHi := (129052750571575077151/20000000000000000000)
  directionLo := (323596398390740532837/50000000000000000000)
  directionHi := (25887711871259242627/4000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree169.table
  base := (261730612153331540452689125540737302984343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28048230000000000000000000000000000000000000000
      center := (409504158)
      previous := (204752079)
      next := (204752079)
      square := (2018863645484223498503678627228100000000000000)
      linear := (-358725098427889285478305384028899986000000000000)
      constant := (16669270165225141123585811578493572398368453886289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree169.table
  base := (261730612153331540415512155150391374735313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (32045454690225769817518708368700000000000000)
      linear := (-5700160309630960773520638377778722000000000000)
      constant := (265134814197505643782795005527750092394590870073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell127.Kernel169
