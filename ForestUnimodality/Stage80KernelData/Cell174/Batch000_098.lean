import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell174.Parameters
import ForestUnimodality.BinomialMassData.Q57_107.Batch000_049
import ForestUnimodality.BinomialMassData.Q57_107.Batch050_099
import ForestUnimodality.BinomialMassData.Q29_54.Batch000_049
import ForestUnimodality.BinomialMassData.Q29_54.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree000.table
  base := (3928408701305821331239087637/100000000000000000000000000)
  polynomial :=
    { denominator := 535000000000000000000000000000000000000000
      center := (2451)
      previous := (0)
      next := (2150)
      square := (97751658237541650953161818900000000000000)
      linear := (-385267139776316257515631491100000000000000)
      constant := (21016986551986144122129118857950000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree000.table
  base := (3928408701305821331239087637/100000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-194433883625430634634057014200000000000000)
      constant := (10606703493525717594345536619900000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree001.table
  base := (58040878467351759983828771982014156461871/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-52367272995145587762833016902300000000000000)
      constant := (1353948440968874111124053830319160154663922158) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree001.table
  base := (115434796873199737652929371764521563183347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-2226786874124172364020068917200000000000000)
      constant := (57169126678299502075213219856307479707106642) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12465659275774314887/25000000000000000000)
  directionHi := (49862637103097259549/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree002.table
  base := (143477685607775370751962366537346034722963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-127021924068450671942986928513800000000000000)
      constant := (1754262361242048201140394030315274751543203387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree002.table
  base := (3551580339388687592332940198036491336647/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-2703668795619469016333624706600000000000000)
      constant := (36913094948843265566238474969314695792208840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12465659275774314887/25000000000000000000)
  centralHi := (49862637103097259549/100000000000000000000)
  directionLo := (35258208823444019841/50000000000000000000)
  directionHi := (70516417646888039683/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree003.table
  base := (46511993336788506567433857299216754095531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-74654651073305084180153911611500000000000000)
      constant := (625110102320473050749287747537532617639734419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree003.table
  base := (11479060419588170986307148892639904752929/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-353394524123862852071908944000000000000000)
      constant := (2920783267984642463999927849360219426632664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35258208823444019841/50000000000000000000)
  centralHi := (70516417646888039683/100000000000000000000)
  directionLo := (21591155215483368161/25000000000000000000)
  directionHi := (17272924172386694529/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree004.table
  base := (3154845875104211725192045046172803555787/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-85798340112384832388814358966100000000000000)
      constant := (496530073808937056506027049023924279102053630) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree004.table
  base := (31085485298148142124843287965534414546393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-3657432638610062320960736285400000000000000)
      constant := (20915426971415893478131253987649725469546998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21591155215483368161/25000000000000000000)
  centralHi := (17272924172386694529/20000000000000000000)
  directionLo := (99725274206194519097/100000000000000000000)
  directionHi := (49862637103097259549/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree005.table
  base := (22189909535913810810611813822381000901959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-96942029151464580597474806320700000000000000)
      constant := (438057880518014461761439993473440079326528591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree005.table
  base := (8734495025262228065728407207548324568739/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-4134314560105358973274292074800000000000000)
      constant := (18512520986679385149139799519921214351017885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99725274206194519097/100000000000000000000)
  centralHi := (49862637103097259549/50000000000000000000)
  directionLo := (111496246099928661853/100000000000000000000)
  directionHi := (55748123049964330927/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree006.table
  base := (15974017357117678047736031160116531828393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-108085718190544328806135253675300000000000000)
      constant := (421502325348465892133133912071174172903271457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree006.table
  base := (31399949461018187632726124522319456753899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-512355164622295069509760873800000000000000)
      constant := (1986514324291049144981978626102625332355273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111496246099928661853/100000000000000000000)
  centralHi := (55748123049964330927/50000000000000000000)
  directionLo := (12213801813215665899/10000000000000000000)
  directionHi := (122138018132156658991/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree007.table
  base := (11585244686534554472201635834040885887433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-119229407229624077014795701029900000000000000)
      constant := (431801819140855033362602603245534102525220417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree007.table
  base := (2273320814797325260554337742485664949829/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-5088078403095952277901403653600000000000000)
      constant := (18377045702292130771021180590390165828084470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12213801813215665899/10000000000000000000)
  centralHi := (122138018132156658991/100000000000000000000)
  directionLo := (26384827497731494757/20000000000000000000)
  directionHi := (65962068744328736893/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree008.table
  base := (64925922344641354080169388148583869643/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-130373096268703825223456148384500000000000000)
      constant := (460792383805269465374605280397681500613466496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree008.table
  base := (13008383530117035543436164213695011829/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-5564960324591248930214959443000000000000000)
      constant := (19664710796486650628964861143109859843058750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26384827497731494757/20000000000000000000)
  centralHi := (65962068744328736893/50000000000000000000)
  directionLo := (35258208823444019841/25000000000000000000)
  directionHi := (28206567058755215873/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree009.table
  base := (230196650743601502136934091746572382859/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-141516785307783573432116595739100000000000000)
      constant := (503952566416819811266743688410762680283817275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree009.table
  base := (5601859389718293419730975413186159112221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-671315805120727286947612803600000000000000)
      constant := (2394728821514669488487841398662052592059934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35258208823444019841/25000000000000000000)
  centralHi := (28206567058755215873/20000000000000000000)
  directionLo := (29917582261858355729/20000000000000000000)
  directionHi := (74793955654645889323/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree010.table
  base := (923232479168654702961811501993054118817/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-152660474346863321640777043093700000000000000)
      constant := (558700509908856411155910517702273906425343332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree010.table
  base := (890018509222946821417138300040298066139/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-6518724167581842234842071021800000000000000)
      constant := (23932996397310040143974633553278339440574216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29917582261858355729/20000000000000000000)
  centralHi := (74793955654645889323/50000000000000000000)
  directionLo := (39419875847051854551/25000000000000000000)
  directionHi := (31535900677641483641/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree011.table
  base := (995211713071318872707086475516640587/2500000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-163804163385943069849437490448300000000000000)
      constant := (623500496046278957659693163394380036161126000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree011.table
  base := (3746781067271131227659936980333990974241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-6995606089077138887155626811200000000000000)
      constant := (26742116154015576157182685431971159806740563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39419875847051854551/25000000000000000000)
  centralHi := (31535900677641483641/20000000000000000000)
  directionLo := (82687829164313665251/50000000000000000000)
  directionHi := (165375658328627330503/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree012.table
  base := (140875495739875320850522480166821547057/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-174947852425022818058097937802900000000000000)
      constant := (697392013103205394711394952865319759569022372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree012.table
  base := (18380704814628047423890241642481690551/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-830276445619159504385464733400000000000000)
      constant := (3326658345732316089751821901817350282243850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82687829164313665251/50000000000000000000)
  centralHi := (165375658328627330503/100000000000000000000)
  directionLo := (21591155215483368161/12500000000000000000)
  directionHi := (172729241723866945289/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree013.table
  base := (-643328169919042571077143362376973333119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-186091541464102566266758385157500000000000000)
      constant := (779739713055236081198643568057946032309120569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree013.table
  base := (-36805164680951605739771933885750349417/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-7949369932067732191782738390000000000000000)
      constant := (33499907794955050203463563304580506603666760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21591155215483368161/12500000000000000000)
  centralHi := (172729241723866945289/100000000000000000000)
  directionLo := (179782294805070360357/100000000000000000000)
  directionHi := (89891147402535180179/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree014.table
  base := (-3337775289412749930897988757832126719119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-394470461006364628950837665024200000000000000)
      constant := (1740198277426280032729129663568779981192806569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree014.table
  base := (-3503525588175397455963822913423929325687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-8426251853563028844096294179400000000000000)
      constant := (37403454979424427026126159242437985173858059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179782294805070360357/100000000000000000000)
  centralHi := (89891147402535180179/50000000000000000000)
  directionLo := (93284452220416131557/50000000000000000000)
  directionHi := (37313780888166452623/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree015.table
  base := (-5083461318325270366193563211865404413139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-416757839084524125368158559733400000000000000)
      constant := (1936286745675562731107406261603352984873971589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree015.table
  base := (-2615719165693741262602323761402021356507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-989237086117591721823316663200000000000000)
      constant := (4626314793184155796439451828634290846748622) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93284452220416131557/50000000000000000000)
  centralHi := (37313780888166452623/20000000000000000000)
  directionLo := (48279290774569931031/25000000000000000000)
  directionHi := (1544937304786237793/800000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree016.table
  base := (-3283733635370357965938069475239538102069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-219522608581341810892739727221300000000000000)
      constant := (1073621952272737188505844269929982528269412019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree016.table
  base := (-6699364394570936888203330240499436679067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-9380015696553622148723405758200000000000000)
      constant := (46189491315273697588384020039558636886986719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48279290774569931031/25000000000000000000)
  centralHi := (1544937304786237793/800000000000000000)
  directionLo := (99725274206194519097/50000000000000000000)
  directionHi := (39890109682477807639/20000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree017.table
  base := (-7824352617563264262744854993011723308347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-461332595240843118202800349151800000000000000)
      constant := (2372674082653633040701161155706208779842735197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree017.table
  base := (-397083299901210566917787593698720884629/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-9856897618048918801036961547600000000000000)
      constant := (51053079489740789744617820951774216500703060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99725274206194519097/50000000000000000000)
  centralHi := (39890109682477807639/20000000000000000000)
  directionLo := (41117783909582439923/20000000000000000000)
  directionHi := (3212326867936128119/1562500000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree018.table
  base := (-8882008167286546398173671519948162034073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-483619973319002614620121243861000000000000000)
      constant := (2612257958133595140406031639035713492871898223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree018.table
  base := (-1797220814281687068262988611488917399031/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-1148197726616023939261168593000000000000000)
      constant := (6246761306239002686278086972248996151130815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41117783909582439923/20000000000000000000)
  centralHi := (3212326867936128119/1562500000000000000)
  directionLo := (105774626470332059523/50000000000000000000)
  directionHi := (211549252940664119047/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree019.table
  base := (-976327117957123805856400318568266992571/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-252953675698581055518721069285100000000000000)
      constant := (1432867033599752799901712096735159556010273105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree019.table
  base := (-4927708374134798854678578833761535889847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-10810661461039512105664073126400000000000000)
      constant := (61687282748052725602655775742941893557534358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105774626470332059523/50000000000000000000)
  centralHi := (211549252940664119047/100000000000000000000)
  directionLo := (217346196190842635799/100000000000000000000)
  directionHi := (1086730980954213179/500000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree020.table
  base := (-2097403785139203914122518565037075041097/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-528194729475321607454763033279400000000000000)
      constant := (3132886283972494807832987810292452639272402235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree020.table
  base := (-10568394607290278388193804414132131879057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-11287543382534808757977628915800000000000000)
      constant := (67447806354826027096268927613365891953389149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217346196190842635799/100000000000000000000)
  centralHi := (1086730980954213179/500000000000000000)
  directionLo := (111496246099928661853/50000000000000000000)
  directionHi := (222992492199857323707/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree021.table
  base := (-11068950365956411104557240321775209873131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-550482107553481103872083927988600000000000000)
      constant := (3413534871056139354065669918637995622162523181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree021.table
  base := (-5570327039206931294785380608136166698877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-1307158367114456156699020522800000000000000)
      constant := (8166514198221631783431998891910646998260642) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111496246099928661853/50000000000000000000)
  centralHi := (222992492199857323707/100000000000000000000)
  directionLo := (114249654437528388551/50000000000000000000)
  directionHi := (228499308875056777103/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree022.table
  base := (-2304434307467432865037917150515464409979/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-572769485631640600289404822697800000000000000)
      constant := (3707529777433000816691271031263942239850752145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree022.table
  base := (-11585219811240892704953712042149130024909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-12241307225525402062604740494600000000000000)
      constant := (79836582045705770665386801780157761403947113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114249654437528388551/50000000000000000000)
  centralHi := (228499308875056777103/100000000000000000000)
  directionLo := (46775299778944772591/20000000000000000000)
  directionHi := (58469124723680965739/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree023.table
  base := (-11857650244120984388725640626759660848767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-595056863709800096706725717407000000000000000)
      constant := (4014745432711846504376274032401828642942466617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree023.table
  base := (-476519156009966492855770931399057825761/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-12718189147020698714918296284000000000000000)
      constant := (86459023576001177098111820088700723708501925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46775299778944772591/20000000000000000000)
  centralHi := (58469124723680965739/25000000000000000000)
  directionLo := (47826561370907251859/20000000000000000000)
  directionHi := (7472900214204258103/3125000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree024.table
  base := (-2416915750233308211787641189157737480759/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-617344241787959593124046612116200000000000000)
      constant := (4335076594652309506995244123385865317913951045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree024.table
  base := (-1516630525371142441221158929103207435731/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-1466119007612888374136872452600000000000000)
      constant := (10373748661166777955886664012913707193882104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47826561370907251859/20000000000000000000)
  centralHi := (7472900214204258103/3125000000000000000)
  directionLo := (12213801813215665899/5000000000000000000)
  directionHi := (244276036264313317981/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree025.table
  base := (-6105334226617831826202091117713448711591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-319815809933059544770683753412700000000000000)
      constant := (2334217487747880820351346185048298725700994641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree025.table
  base := (-3063262491900474129343938689752537324007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-13671952990011292019545407862800000000000000)
      constant := (100548870046892383638478087132310533721065196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12213801813215665899/5000000000000000000)
  centralHi := (244276036264313317981/100000000000000000000)
  directionLo := (249313185515486297743/100000000000000000000)
  directionHi := (15582074094717893609/6250000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree026.table
  base := (-3060598054161934496477779062574720886221/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-330959498972139292979344200767300000000000000)
      constant := (2507373233697856128641109074870164041147311542) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree026.table
  base := (-47966387120374727718435380045306602559/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-14148834911506588671858963652200000000000000)
      constant := (108012864930368878430761659768141566868009728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249313185515486297743/100000000000000000000)
  centralHi := (15582074094717893609/6250000000000000000)
  directionLo := (50850111917577706807/20000000000000000000)
  directionHi := (63562639896972133509/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree027.table
  base := (-12185185267102574465582389488942178617933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-684206376022438082376009296243800000000000000)
      constant := (5373948842453124227394114867540300997003285083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree027.table
  base := (-12217444811842417154754107303962343292161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-1625079648111320591574724382400000000000000)
      constant := (12861602095171701126835304228143016731111653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50850111917577706807/20000000000000000000)
  centralHi := (63562639896972133509/25000000000000000000)
  directionLo := (64773465646450104483/25000000000000000000)
  directionHi := (259093862585800417933/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree028.table
  base := (-3010903138848521419235427618973939108869/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-353246877050298789396665095476500000000000000)
      constant := (2872994918273179022923360792299534742285117638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree028.table
  base := (-301792461997994857347289890630298163051/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-15102598754497181976486075231000000000000000)
      constant := (123772438474808738531143432516273501855144280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64773465646450104483/25000000000000000000)
  centralHi := (259093862585800417933/100000000000000000000)
  directionLo := (263848274977314947571/100000000000000000000)
  directionHi := (65962068744328736893/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree029.table
  base := (-11821508638350537674316582896855972981511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-728781132178757075210651085662200000000000000)
      constant := (6130825547834286894584042711219095965334680561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree029.table
  base := (-2369185972405976301169583585527451454709/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-15579480675992478628799631020400000000000000)
      constant := (132066006762698581390057356208734146482528565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263848274977314947571/100000000000000000000)
  centralHi := (65962068744328736893/25000000000000000000)
  directionLo := (134259259259259259259/50000000000000000000)
  directionHi := (268518518518518518519/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree030.table
  base := (-11522094821292415652185759078063590636301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-751068510256916571627971980371400000000000000)
      constant := (6528419095592296538614491012017249950804989851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree030.table
  base := (-11543304348659225765375700531204665126137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-1784040288609752809012576312200000000000000)
      constant := (15626039392258511978154957881657474041594301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134259259259259259259/50000000000000000000)
  centralHi := (268518518518518518519/100000000000000000000)
  directionLo := (273108911180604182117/100000000000000000000)
  directionHi := (136554455590302091059/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree031.table
  base := (-11148077380025840899235362394247542731873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-773355888335076068045292875080600000000000000)
      constant := (6938739495668682695303899060476259883262786023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree031.table
  base := (-1116647716522192819400644248801118084523/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-16533244518983071933426742599200000000000000)
      constant := (149476836557917191198623072425163283054609110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273108911180604182117/100000000000000000000)
  centralHi := (136554455590302091059/50000000000000000000)
  directionLo := (8675731684354716357/3125000000000000000)
  directionHi := (11104936555974036937/4000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree032.table
  base := (-10701729981886751108087628222011464660591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-795643266413235564462613769789800000000000000)
      constant := (7361760716846116214009434883769390741100893641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree032.table
  base := (-5358837830456996803192740854092670121117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-17010126440478368585740298388600000000000000)
      constant := (158592911599615702405783893567310962321137138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8675731684354716357/3125000000000000000)
  centralHi := (11104936555974036937/4000000000000000000)
  directionLo := (35258208823444019841/12500000000000000000)
  directionHi := (282065670587552158729/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree033.table
  base := (-10184962880850442738659893405175883714249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-817930644491395060879934664499000000000000000)
      constant := (7797460888626833925561504892371741307355563199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree033.table
  base := (-10198768293710398629893973576372283315909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-1943000929108185026450428242000000000000000)
      constant := (18664680624459358011602607066987948350470457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35258208823444019841/12500000000000000000)
  centralHi := (282065670587552158729/100000000000000000000)
  directionLo := (11457561702413347837/4000000000000000000)
  directionHi := (143219521280166847963/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree034.table
  base := (-9599381026288657147772113899637355903467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-840218022569554557297255559208200000000000000)
      constant := (8245821635945478763165877410544251912261206317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree034.table
  base := (-1922264495453763771689793381696361722801/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-17963890283468961890367409967400000000000000)
      constant := (177644097737953935125219939669638920506796785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11457561702413347837/4000000000000000000)
  centralHi := (143219521280166847963/50000000000000000000)
  directionLo := (290746638298288549453/100000000000000000000)
  directionHi := (145373319149144274727/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree035.table
  base := (-1789266574117066857273804495906701058749/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-862505400647714053714576453917400000000000000)
      constant := (8706827520370706998324186192755820897891913495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree035.table
  base := (-279895409242091313374761334224808850299/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-18440772204964258542680965756800000000000000)
      constant := (187578508436224528208339439826817886380074976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290746638298288549453/100000000000000000000)
  centralHi := (145373319149144274727/50000000000000000000)
  directionLo := (147495669648833251239/50000000000000000000)
  directionHi := (294991339297666502479/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree036.table
  base := (-1028368921131730595947050713037653901399/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-442396389362936775065948674313300000000000000)
      constant := (4590232785348567925443377054343727601931531396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree036.table
  base := (-8235863195984302894022564248159991730663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-2101961569606617243888280171800000000000000)
      constant := (21976121074951553314243983563299680223272099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147495669648833251239/50000000000000000000)
  centralHi := (294991339297666502479/100000000000000000000)
  directionLo := (299175822618583557291/100000000000000000000)
  directionHi := (74793955654645889323/25000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree037.table
  base := (-232568388236378252460065374350901233033/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-453540078402016523274609121667900000000000000)
      constant := (4833362444300128329219582425463504508528082928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree037.table
  base := (-7449878120428165534862238993874158831339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-19394536047954851847308077335600000000000000)
      constant := (208263616594757619393756768213638579403984623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299175822618583557291/100000000000000000000)
  centralHi := (74793955654645889323/25000000000000000000)
  directionLo := (303302580632577777457/100000000000000000000)
  directionHi := (151651290316288888729/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree038.table
  base := (-6592843819549064224903646761648788356099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-929367534882192542966539138045000000000000000)
      constant := (10165596317336647553475056392553483022111022549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree038.table
  base := (-6599474139151206924781975291011649015091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-19871417969450148499621633125000000000000000)
      constant := (219013900563177781540274435287484169289332887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303302580632577777457/100000000000000000000)
  centralHi := (151651290316288888729/50000000000000000000)
  directionLo := (307373938383293185429/100000000000000000000)
  directionHi := (30737393838329318543/10000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree039.table
  base := (-709948692175196086857422605494109664977/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-475827456480176019691930016377100000000000000)
      constant := (5338536081701395435445931906652391753782713308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree039.table
  base := (-1421325617008179260710682386802352259057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-2260922210105049461326132101600000000000000)
      constant := (25559531481596199866981893431575345956021844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307373938383293185429/100000000000000000000)
  centralHi := (30737393838329318543/10000000000000000000)
  directionLo := (311392068903708090641/100000000000000000000)
  directionHi := (155696034451854045321/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree040.table
  base := (-587873772250554164664687960605117900201/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-486971145519255767900590463731700000000000000)
      constant := (5600572981341589626133238921544128020642395004) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree040.table
  base := (-1176977354215687401705505319479822708923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-20825181812440741804248744703800000000000000)
      constant := (241329132155042688128024647761465612326926844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311392068903708090641/100000000000000000000)
  centralHi := (155696034451854045321/50000000000000000000)
  directionLo := (315359006776414836409/100000000000000000000)
  directionHi := (31535900677641483641/10000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree041.table
  base := (-114485003864742848386396202493837700993/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-498114834558335516109250911086300000000000000)
      constant := (5868906141987349208609881137489368834581298288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree041.table
  base := (-1833876645549290136367461862247907169701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-21302063733936038456562300493200000000000000)
      constant := (252893835656982331531425593121697517115525314) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315359006776414836409/100000000000000000000)
  centralHi := (31535900677641483641/10000000000000000000)
  directionLo := (159638330088580253679/50000000000000000000)
  directionHi := (319276660177160507359/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree042.table
  base := (-160098622272793176740310779005407627153/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-509258523597415264317911358440900000000000000)
      constant := (6143533281956237816467071191599936704613802424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree042.table
  base := (-20040770081319560681589519046358273391/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-2419882850603481678763984031400000000000000)
      constant := (29414422267958359577162333969775785807160704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159638330088580253679/50000000000000000000)
  centralHi := (319276660177160507359/100000000000000000000)
  directionLo := (161573410801992109247/50000000000000000000)
  directionHi := (64629364320796843699/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree043.table
  base := (-1397498571578455077800335158864481620169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1040804425272990025053143611591000000000000000)
      constant := (12848904968277985636504959887683760549930685119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree043.table
  base := (-1400627802804930557719831492406228632477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-22255827576926631761189412072000000000000000)
      constant := (276836948039804677973559439504295286442308089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161573410801992109247/50000000000000000000)
  centralHi := (64629364320796843699/20000000000000000000)
  directionLo := (65394235492628055683/20000000000000000000)
  directionHi := (20435698591446267401/6250000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree044.table
  base := (-171563356202719067219680438192899417567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1063091803351149521470464506300200000000000000)
      constant := (13423324275472728765902460713486329494568275417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree044.table
  base := (-34850316486957683849815155024070796367/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-22732709498421928413502967861400000000000000)
      constant := (289215212787142661819375231459045753982414095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65394235492628055683/20000000000000000000)
  centralHi := (20435698591446267401/6250000000000000000)
  directionLo := (66150263331450932201/20000000000000000000)
  directionHi := (165375658328627330503/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree045.table
  base := (557995630110244685902325421598345177831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-542689590714654508943892700504700000000000000)
      constant := (7005160889307439172238509825080879453940987119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree045.table
  base := (556841540098788695255904855464751037831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-2578843491101913896201835961200000000000000)
      constant := (33540504387787414337144192314945096556042874) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66150263331450932201/20000000000000000000)
  centralHi := (165375658328627330503/50000000000000000000)
  directionLo := (334488738299785985559/100000000000000000000)
  directionHi := (8362218457494649639/2500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree046.table
  base := (616241655218903372584984382651666399407/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-553833279753734257152553147859300000000000000)
      constant := (7304947601641276531505052986604957857213621486) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree046.table
  base := (1231492868289943209229556372814278171287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-23686473341412521718130079440200000000000000)
      constant := (314784881869648395468222735561187739191245482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334488738299785985559/100000000000000000000)
  centralHi := (8362218457494649639/2500000000000000000)
  directionLo := (4227310733275387567/1250000000000000000)
  directionHi := (338184858662031005361/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree047.table
  base := (3875195805274469076819803429680368150521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1129953937585628010722427190427800000000000000)
      constant := (15222042638403083700463496241581610534955314929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree047.table
  base := (484187076228659784396249572073812680431/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-24163355262907818370443635229600000000000000)
      constant := (327976201100045126046520496308261491850757864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4227310733275387567/1250000000000000000)
  centralHi := (338184858662031005361/100000000000000000000)
  directionLo := (68368203488795303867/20000000000000000000)
  directionHi := (42730127180497064917/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree048.table
  base := (42772308460580386769977478212459742987/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1152241315663787507139748085137000000000000000)
      constant := (15846762478187306487206759072244406449682270375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree048.table
  base := (2672540826675921876326345586308458296911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-2737804131600346113639687891000000000000000)
      constant := (37937607178661622314627668106460656748033194) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68368203488795303867/20000000000000000000)
  centralHi := (42730127180497064917/12500000000000000000)
  directionLo := (21591155215483368161/6250000000000000000)
  directionHi := (345458483447733890577/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree049.table
  base := (6878877025422277586672764439282430517179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1174528693741947003557068979846200000000000000)
      constant := (16484053373343694051811786733354544546991182371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree049.table
  base := (6877628405622053945050611818738356165141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-25117119105898411675070746808400000000000000)
      constant := (355171645065226116299485135425103420548129263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21591155215483368161/6250000000000000000)
  centralHi := (345458483447733890577/100000000000000000000)
  directionLo := (8725961493042020421/2500000000000000000)
  directionHi := (349038459721680816841/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree050.table
  base := (4236056089912689207435799394244172971357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-598408035910053249987194937277700000000000000)
      constant := (8566957095044622552534518422649701536349066293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree050.table
  base := (8471042512815100068724449900213012446739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-25594001027393708327384302597800000000000000)
      constant := (369175719543880243915604511715751762024557577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8725961493042020421/2500000000000000000)
  centralHi := (349038459721680816841/100000000000000000000)
  directionLo := (35258208823444019841/10000000000000000000)
  directionHi := (352582088234440198411/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree051.table
  base := (2531540201787223858880517193997393326437/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-609551724949132998195855384632300000000000000)
      constant := (8898171987855537970328736095798152312388754426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree051.table
  base := (10125244811690871155164409676216904408829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-2896764772098778331077539820800000000000000)
      constant := (42605629867472181857184362385007856419038383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35258208823444019841/10000000000000000000)
  centralHi := (352582088234440198411/100000000000000000000)
  directionLo := (356090454130174268641/100000000000000000000)
  directionHi := (178045227065087134321/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree052.table
  base := (1480119122732899421731756743233988963093/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-620695413988212746404515831986900000000000000)
      constant := (9235670964815898893607124831572743758553807028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree052.table
  base := (11840168882464421114892281821684080164901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-26547764870384301632011414176600000000000000)
      constant := (397996476715326552796906179807069231480070943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356090454130174268641/100000000000000000000)
  centralHi := (178045227065087134321/50000000000000000000)
  directionLo := (179782294805070360357/50000000000000000000)
  directionHi := (71912917922028144143/20000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree053.table
  base := (1702053742896769161536206254836654106253/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-631839103027292494613176279341500000000000000)
      constant := (9579453689549539354164519917040299411449962388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree053.table
  base := (13615758995940796688373338803686074700181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-27024646791879598284324969966000000000000000)
      constant := (412813129725916618520278327951245716152143983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179782294805070360357/50000000000000000000)
  centralHi := (71912917922028144143/20000000000000000000)
  directionLo := (363005477479864052521/100000000000000000000)
  directionHi := (181502738739932026261/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree054.table
  base := (3863135577750026992858221420426597688299/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-642982792066372242821836726696100000000000000)
      constant := (9929519879380181882350489114077528233866670502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree054.table
  base := (3090393678278407601311400777760981385973/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-3055725412597210548515391750600000000000000)
      constant := (47544512941795882181844046194597732487106355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363005477479864052521/100000000000000000000)
  centralHi := (181502738739932026261/50000000000000000000)
  directionLo := (36641405439646997697/10000000000000000000)
  directionHi := (366414054396469976971/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree055.table
  base := (2168656073382532228929757010468378987139/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-654126481105451991030497174050700000000000000)
      constant := (10285869296750918029521205685607409884095017644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree055.table
  base := (17348757831888531134041802799170628403053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-27978410634870191588952081544800000000000000)
      constant := (443258927431491619959557884957948462701941879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36641405439646997697/10000000000000000000)
  centralHi := (366414054396469976971/100000000000000000000)
  directionLo := (184895606923294983087/50000000000000000000)
  directionHi := (14791648553863598647/4000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree056.table
  base := (19306513895508586249113593531596964030531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1330540340289063478478315242810600000000000000)
      constant := (21297003484029934547034419004511253641185549419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree056.table
  base := (19306094392382367512939622586837518998001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-28455292556365488241265637334200000000000000)
      constant := (458888054591116017709595924124601517116514243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184895606923294983087/50000000000000000000)
  centralHi := (14791648553863598647/4000000000000000000)
  directionLo := (373137808881664526229/100000000000000000000)
  directionHi := (37313780888166452623/10000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree057.table
  base := (10662154462414816949461667020822244227029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-676413859183611487447818068759900000000000000)
      constant := (11017417047378559367429468793297993874155255021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree057.table
  base := (21323950443042605668822496771307524932703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-3214686053095642765953243680400000000000000)
      constant := (52754221248998579345380504155175303173182981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373137808881664526229/100000000000000000000)
  centralHi := (37313780888166452623/10000000000000000000)
  directionLo := (376454654634372629193/100000000000000000000)
  directionHi := (188227327317186314597/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree058.table
  base := (23402609038830849119165202790844019770343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1375115096445382471312957032229000000000000000)
      constant := (22785230143623620098541140062819973182350657007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree058.table
  base := (2925287849548023942420721256511595797807/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-29409056399356081545892748913000000000000000)
      constant := (490958731746546341018898833535858542230936808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376454654634372629193/100000000000000000000)
  centralHi := (188227327317186314597/50000000000000000000)
  directionLo := (379742530637219966807/100000000000000000000)
  directionHi := (47467816329652495851/12500000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree059.table
  base := (2554139352970683954814094372827314800767/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-698701237261770983865138963469100000000000000)
      constant := (11774095696772887350465971549828099635769906915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree059.table
  base := (2554113199180072617449398102216878747917/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-29885938320851378198206304702400000000000000)
      constant := (507400271378866043496150475420537015357438310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (379742530637219966807/100000000000000000000)
  centralHi := (47467816329652495851/12500000000000000000)
  directionLo := (191501091480985504981/50000000000000000000)
  directionHi := (383002182961971009963/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree060.table
  base := (27740644990469889133522207410933497410711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1419689852601701464147598821647400000000000000)
      constant := (24323717645230980180948239424331777611855230239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree060.table
  base := (5548084339072620862953812652684446651663/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-3373646693594074983391095610200000000000000)
      constant := (58234734018755727662459556990112400297974505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191501091480985504981/50000000000000000000)
  centralHi := (383002182961971009963/100000000000000000000)
  directionLo := (386234326196559448249/100000000000000000000)
  directionHi := (1544937304786237793/400000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree061.table
  base := (7500087196917472467218182904309847633247/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-720988615339930480282459858178300000000000000)
      constant := (12555904365570433126012170135335886891106089806) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree061.table
  base := (30000158196312848351724331358104144455077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-30839702163841971502833416281200000000000000)
      constant := (541095732784638547357998041450769307102583711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386234326196559448249/100000000000000000000)
  centralHi := (1544937304786237793/400000000000000000)
  directionLo := (77887929054863298383/20000000000000000000)
  directionHi := (97359911318579122979/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree062.table
  base := (32320492618375680288273570664432271545423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1464264608758020456982240611065800000000000000)
      constant := (25912464510419174046536939629554285076923547927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree062.table
  base := (32320329984671096986357871135091494904277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-31316584085337268155146972070600000000000000)
      constant := (558349648429452175388079095896227233261739311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77887929054863298383/20000000000000000000)
  centralHi := (97359911318579122979/25000000000000000000)
  directionLo := (196309398584390650031/50000000000000000000)
  directionHi := (392618797168781300063/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree063.table
  base := (34701066137951366458832771074041001192147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1486551986836179953399561505775000000000000000)
      constant := (26725684864630167214848357525604295422648891003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree063.table
  base := (17350463698447131371434228785762571850839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-3532607334092507200828947540000000000000000)
      constant := (63986038972777926810639942062981178879945306) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196309398584390650031/50000000000000000000)
  centralHi := (392618797168781300063/100000000000000000000)
  directionLo := (395772412465972421357/100000000000000000000)
  directionHi := (197886206232986210679/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree064.table
  base := (37142060647313397519637793955663359801803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1508839364914339449816882400484200000000000000)
      constant := (27551469694178038183152006301065589806370842547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree064.table
  base := (37141942318613016950335192160195879805883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-32270347928327861459774083649400000000000000)
      constant := (593669837789494298214005411125327598792829569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (395772412465972421357/100000000000000000000)
  centralHi := (197886206232986210679/50000000000000000000)
  directionLo := (99725274206194519097/25000000000000000000)
  directionHi := (398901096824778076389/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree065.table
  base := (39643468830162403385437488329841623528063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1531126742992498946234203295193400000000000000)
      constant := (28389818915298475463341845528374356747772793287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree065.table
  base := (9910841983814412758457660503288899260311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-32747229849823158112087639438800000000000000)
      constant := (611736107876990606959109527379946810081022292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99725274206194519097/25000000000000000000)
  centralHi := (398901096824778076389/100000000000000000000)
  directionLo := (201002716167522314283/50000000000000000000)
  directionHi := (402005432335044628567/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree066.table
  base := (42205284532203047653078486452905886753391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1553414121070658442651524189902600000000000000)
      constant := (29240732457530951748938172300233319497439573559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree066.table
  base := (4220519852285465771205864440081143000001/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-3691567974590939418266799469800000000000000)
      constant := (70008128847396078362412984420821908610000270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201002716167522314283/50000000000000000000)
  centralHi := (402005432335044628567/100000000000000000000)
  directionLo := (81017195756397620917/20000000000000000000)
  directionHi := (202542989390994052293/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree067.table
  base := (44827502575641589534106499437890919612269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1575701499148817939068845084611800000000000000)
      constant := (30104210261594906501653973463175613138640867781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree067.table
  base := (44827429272522427556594106678695188110919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-33700993692813751416714751017600000000000000)
      constant := (648680991869658362030720110835072930710953317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81017195756397620917/20000000000000000000)
  centralHi := (202542989390994052293/50000000000000000000)
  directionLo := (408143274824707222371/100000000000000000000)
  directionHi := (102035818706176805593/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree068.table
  base := (47510118603323289186981440810372389724197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1597988877226977435486165979321000000000000000)
      constant := (30980252277605275105043456567155553489952331453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree068.table
  base := (11877514035809182620944606405454671182753/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-34177875614309048069028306807000000000000000)
      constant := (667559603624302689355790239939301940389635916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408143274824707222371/100000000000000000000)
  centralHi := (102035818706176805593/25000000000000000000)
  directionLo := (411177839095824399231/100000000000000000000)
  directionHi := (3212326867936128119/781250000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree069.table
  base := (50253128947772834010484504122157086267327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1620276255305136931903486874030200000000000000)
      constant := (31868858463573132705135267497147776480674626823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree069.table
  base := (25126537869155708022969347146059047430333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-3850528615089371635704651399600000000000000)
      constant := (76300999340566994742015858968237188561237982) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411177839095824399231/100000000000000000000)
  centralHi := (3212326867936128119/781250000000000000)
  directionLo := (414190171228611883481/100000000000000000000)
  directionHi := (207095085614305941741/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree070.table
  base := (10611306104231600343018221199717975969467/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1642563633383296428320807768739400000000000000)
      constant := (32770028784145888188936639298095855534372138415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree070.table
  base := (53056485201773589989891145088303977434373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-35131639457299641373655418385800000000000000)
      constant := (706129162498057738694253927632457866516552639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414190171228611883481/100000000000000000000)
  centralHi := (207095085614305941741/50000000000000000000)
  directionLo := (417180752817363330889/100000000000000000000)
  directionHi := (41718075281736333089/10000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree071.table
  base := (55920320722832823992248917512979017284259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1664851011461455924738128663448600000000000000)
      constant := (33683763209548745865282956356118096768887481291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree071.table
  base := (447362257051424922961601800825340441341/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-35608521378794938025968974175200000000000000)
      constant := (725820108339433629126382991337819715905732875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417180752817363330889/100000000000000000000)
  centralHi := (41718075281736333089/10000000000000000000)
  directionLo := (420150048316238057541/100000000000000000000)
  directionHi := (210075024158119028771/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree072.table
  base := (58844497361650908908509032121123908775837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1687138389539615421155449558157800000000000000)
      constant := (34610061714695270692928162140189947631574557813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree072.table
  base := (58844464505922693882374606369993353771551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-4009489255587803853142503329400000000000000)
      constant := (82864647899782446165170947681589820551831877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420150048316238057541/100000000000000000000)
  centralHi := (210075024158119028771/50000000000000000000)
  directionLo := (105774626470332059523/25000000000000000000)
  directionHi := (423098505881328238093/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree073.table
  base := (30914529295344283504377574363238399922107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-854712883808887458786385226433500000000000000)
      constant := (17774462139220016675650315059528516440708203043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree073.table
  base := (30914515311778993611893993385668664551809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-36562285221785531330596085754000000000000000)
      constant := (766014330360369958567182349607384970972179174) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105774626470332059523/25000000000000000000)
  centralHi := (423098505881328238093/100000000000000000000)
  directionLo := (17041062326410875123/4000000000000000000)
  directionHi := (106506639540067969519/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree074.table
  base := (32437001426197307666764714200667776642373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-865856572847967206995045673788100000000000000)
      constant := (18250175441475315173348763747418045374778528477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree074.table
  base := (64873979050950644746369262568010498786483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-37039167143280827982909641543400000000000000)
      constant := (786517605778105304160833174548426551205115369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17041062326410875123/4000000000000000000)
  centralHi := (106506639540067969519/25000000000000000000)
  directionLo := (428934623033350723023/100000000000000000000)
  directionHi := (26808413939584420189/6250000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree075.table
  base := (33989664416250336734200399437937436668219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-877000261887046955203706121142700000000000000)
      constant := (18732170756590001495877016460554945712414439331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree075.table
  base := (33989654289980979068164361630957189273671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-4168449896086236070580355259200000000000000)
      constant := (89699073006407816238582233811821688220778234) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428934623033350723023/100000000000000000000)
  centralHi := (26808413939584420189/6250000000000000000)
  directionLo := (21591155215483368161/5000000000000000000)
  directionHi := (431823104309667363221/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree076.table
  base := (71145035421292051827713132681159114581883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1776287901852253406824733136994600000000000000)
      constant := (38440896156423027805403969394486590702847978467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree076.table
  base := (71145018191560600176597129709293452887813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-37992930986271421287536753122200000000000000)
      constant := (828336483951440472012655313769358309051738559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21591155215483368161/5000000000000000000)
  centralHi := (431823104309667363221/100000000000000000000)
  directionLo := (217346196190842635799/50000000000000000000)
  directionHi := (434692392381685271599/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree077.table
  base := (74371121681063060179274307034702453939651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1798575279930412903242054031703800000000000000)
      constant := (39430014801943912340178969301229508395155064299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree077.table
  base := (74371107025502436701380753925406464604209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-38469812907766717939850308911600000000000000)
      constant := (849652086250376357154790927037023770898822787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217346196190842635799/50000000000000000000)
  centralHi := (434692392381685271599/100000000000000000000)
  directionLo := (218771432420567769967/50000000000000000000)
  directionHi := (87508572968227107987/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree078.table
  base := (77657586818768535664393767186243286221439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1820862658008572399659374926413000000000000000)
      constant := (40431697440663082526509884480002899383949255111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree078.table
  base := (3882878717744518372957653562879349915251/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-4327410536584668288018207189000000000000000)
      constant := (96804273753093556245836222068754848954235540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218771432420567769967/50000000000000000000)
  centralHi := (87508572968227107987/20000000000000000000)
  directionLo := (440374887059041293017/100000000000000000000)
  directionHi := (220187443529520646509/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree079.table
  base := (40502215081520659466733917261989239426639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-921575018043365948038347910561100000000000000)
      constant := (20722972032447027878501551207190114802195589911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree079.table
  base := (20251104891207030487011053697199245689759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-39423576750757311244477420490400000000000000)
      constant := (893095616384417625453906150853827666810445748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440374887059041293017/100000000000000000000)
  centralHi := (220187443529520646509/50000000000000000000)
  directionLo := (443188812732382208033/100000000000000000000)
  directionHi := (221594406366191104017/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree080.table
  base := (42205825572439047927673818673619362633791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-932718707082445696247008357915700000000000000)
      constant := (21236377334061156544085549836130268082794273159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree080.table
  base := (42205821067254291132702061158099745983441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-39900458672252607896790976279800000000000000)
      constant := (915223543943547085228587418626836476547952326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443188812732382208033/100000000000000000000)
  centralHi := (221594406366191104017/50000000000000000000)
  directionLo := (111496246099928661853/25000000000000000000)
  directionHi := (445984984399714647413/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree081.table
  base := (87879249281407504568189574569138461760199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1887724792243050888911337610540600000000000000)
      constant := (43512129244819460298057628864800066248692518351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree081.table
  base := (21969810405545861445425294304424478534429/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-4486371177083100505456059118800000000000000)
      constant := (104180249594209505333065957677627843681718332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111496246099928661853/25000000000000000000)
  centralHi := (445984984399714647413/100000000000000000000)
  directionLo := (448763733927875335937/100000000000000000000)
  directionHi := (224381866963937667969/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree082.table
  base := (5712951510140504543869472762429382083787/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-955006085160605192664329252624900000000000000)
      constant := (22282033895143519954748810117643031963818218904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree082.table
  base := (45703608826275081858117529977571582313191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-40854222515243201201418087858600000000000000)
      constant := (960291723506234494407214574621499789004210826) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (448763733927875335937/100000000000000000000)
  centralHi := (224381866963937667969/50000000000000000000)
  directionLo := (451525382971726253267/100000000000000000000)
  directionHi := (112881345742931563317/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree083.table
  base := (94995575438042245019688439391804411157701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1932299548399369881745979399959000000000000000)
      constant := (45628570300525257272584662448514368703344518749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree083.table
  base := (94995569906166855452341919670775242282481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-41331104436738497853731643648000000000000000)
      constant := (983231975340969547467600969436948383874642883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451525382971726253267/100000000000000000000)
  centralHi := (112881345742931563317/25000000000000000000)
  directionLo := (454270243408743681079/100000000000000000000)
  directionHi := (11356756085218592027/2500000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree084.table
  base := (98644302810818879991288933833101220058419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1954586926477529378163300294668200000000000000)
      constant := (46705636772122640787939137736446375868448839131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree084.table
  base := (12330537263821077038573885301344576275527/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-4645331817581532722893911048600000000000000)
      constant := (111827000198431303926796127752690428475513832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454270243408743681079/100000000000000000000)
  centralHi := (11356756085218592027/2500000000000000000)
  directionLo := (91399723550022710841/20000000000000000000)
  directionHi := (228499308875056777103/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree085.table
  base := (102353406025892145044327603175182928487653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-1976874304555688874580621189377400000000000000)
      constant := (47795267202163292358439805146746669348255139197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree085.table
  base := (10235340203281124933316486528167912355239/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-42284868279729091158358755226800000000000000)
      constant := (1029924802784365618168615418690198027023230770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91399723550022710841/20000000000000000000)
  centralHi := (228499308875056777103/50000000000000000000)
  directionLo := (229855399764933505227/50000000000000000000)
  directionHi := (91942159905973402091/20000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree086.table
  base := (53061442432525706649066482925143795130611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-999580841316924185498971042043300000000000000)
      constant := (24448730794074459258464928443472971310450365339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree086.table
  base := (106122881473212587652388566579289520649847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-42761750201224387810672311016200000000000000)
      constant := (1053677378287898429399648823670767353517912821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229855399764933505227/50000000000000000000)
  centralHi := (91942159905973402091/20000000000000000000)
  directionLo := (7225110526148016629/1562500000000000000)
  directionHi := (462407073673473064257/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree087.table
  base := (10995273914083597840840684005394850923857/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-1010724530356003933707631489397900000000000000)
      constant := (25006109963966640818236711536782428241136193965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree087.table
  base := (109952736260098598794270531951718792606493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-4804292458079964940331762978400000000000000)
      constant := (119744525361640375460396821412046407400375311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7225110526148016629/1562500000000000000)
  centralHi := (462407073673473064257/100000000000000000000)
  directionLo := (465087716847198532521/100000000000000000000)
  directionHi := (232543858423599266261/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree088.table
  base := (56921484345860675449630415932872068477271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-1021868219395083681916291936752500000000000000)
      constant := (25569771109833543918530528742304252311996275679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree088.table
  base := (113842966245392521974902652435254182771537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-43715514044214981115299422595000000000000000)
      constant := (1101994852648977814529893455324966766413483491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465087716847198532521/100000000000000000000)
  centralHi := (232543858423599266261/50000000000000000000)
  directionLo := (467752997789447725911/100000000000000000000)
  directionHi := (58469124723680965739/12500000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree089.table
  base := (58896786689035790328742737819189859623807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-1033011908434163430124952384107100000000000000)
      constant := (26139714230875822562923312473940504702832966343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree089.table
  base := (117793571300911344724937175768819489164339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-44192395965710277767612978384400000000000000)
      constant := (1126559751439393263528563507720973135866934377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467752997789447725911/100000000000000000000)
  centralHi := (58469124723680965739/12500000000000000000)
  directionLo := (94080635525041020129/20000000000000000000)
  directionHi := (235201588812602550323/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree090.table
  base := (12180455307873530765351451436099321342793/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-1044155597473243178333612831461700000000000000)
      constant := (26715939326399945790925810693432505650268185285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree090.table
  base := (60902275657627891364207681612070109464121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-4963253098578397157769614908200000000000000)
      constant := (127932824955437744450089286265051785911062534) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94080635525041020129/20000000000000000000)
  centralHi := (235201588812602550323/50000000000000000000)
  directionLo := (236519255082311127307/50000000000000000000)
  directionHi := (94607702032924450923/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree091.table
  base := (31468976922045695869354006905032305607549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-1055299286512322926542273278816300000000000000)
      constant := (27298446395801808557765368122373429733801657002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree091.table
  base := (12587590619119826271978199079873455180321/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-45146159808700871072240089963200000000000000)
      constant := (1176501872103990823793083741885842496088180030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236519255082311127307/50000000000000000000)
  centralHi := (94607702032924450923/20000000000000000000)
  directionLo := (95131848437343127989/20000000000000000000)
  directionHi := (237829621093357819973/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree092.table
  base := (130007637114097523976708585277472807180711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-2132885951102805349501867452341800000000000000)
      constant := (55774470877105890299822209627872986169411960239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree092.table
  base := (4062738620109024691582309017722830138957/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-45623041730196167724553645752600000000000000)
      constant := (1201879093933830886075282033930212727160529632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95131848437343127989/20000000000000000000)
  centralHi := (237829621093357819973/50000000000000000000)
  directionLo := (478265613709072518591/100000000000000000000)
  directionHi := (7472900214204258103/1562500000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree093.table
  base := (134199741275350047253993142929847441202157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-2155173329180964845919188347051000000000000000)
      constant := (56964612908377859696482719876871423354323495493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree093.table
  base := (134199740197011486868977393448839324531753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-5122213739076829375207466838000000000000000)
      constant := (136391898896689636502338221376668661762357331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478265613709072518591/100000000000000000000)
  centralHi := (7472900214204258103/1562500000000000000)
  directionLo := (480857858244399440013/100000000000000000000)
  directionHi := (240428929122199720007/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree094.table
  base := (138452220100292740856305443305162263868293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-2177460707259124342336509241760200000000000000)
      constant := (58167318884599231790538279210234002759028086557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree094.table
  base := (27690443837047081886692605540857176098559/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-46576805573186761029180757331400000000000000)
      constant := (1253445860496951331859541694174541468959749185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (480857858244399440013/100000000000000000000)
  centralHi := (240428929122199720007/50000000000000000000)
  directionLo := (24171810152234467997/5000000000000000000)
  directionHi := (483436203044689359941/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree095.table
  base := (71382536762662319737669106684888028268049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-1099874042668641919376915068234700000000000000)
      constant := (29691294402520919565087038829499283035640893001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree095.table
  base := (14276507274891233846221513020593355589787/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-47053687494682057681494313120800000000000000)
      constant := (1279635405199667378785839353629791854083182410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24171810152234467997/5000000000000000000)
  centralHi := (483436203044689359941/100000000000000000000)
  directionLo := (243000434666864993983/50000000000000000000)
  directionHi := (486000869333729987967/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree096.table
  base := (18392287686710384485117300744934158882063/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-1111017731707721667585575515589300000000000000)
      constant := (30305211334527902969136046493091004740162957148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree096.table
  base := (147138300834981848771309959461540113778107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1247)
      previous := (0)
      next := (1075)
      square := (49332612568478964032436805800000000000000)
      linear := (-5281174379575261592645318767800000000000000)
      constant := (145121747129495687331138166841461583072008889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243000434666864993983/50000000000000000000)
  centralHi := (486000869333729987967/100000000000000000000)
  directionLo := (12213801813215665899/2500000000000000000)
  directionHi := (488552072528626635961/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree097.table
  base := (18946487994303255227943331203506144178589/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (262257)
      previous := (0)
      next := (230050)
      square := (10459427431416956651988314622300000000000000)
      linear := (-1122161420746801415794235962943900000000000000)
      constant := (30925410238028948581191559974048367378802661844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree097.table
  base := (151571903395650359659723711414165092940589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-48007451337672650986121424699600000000000000)
      constant := (1332826817382718913332405353618792117584563127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell174.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12213801813215665899/2500000000000000000)
  centralHi := (488552072528626635961/100000000000000000000)
  directionLo := (491090022450967366803/100000000000000000000)
  directionHi := (122772505612741841701/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree098.table
  base := (31213176172314974242212751302920258696561/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (524514)
      previous := (0)
      next := (460100)
      square := (20918854862833913303976629244600000000000000)
      linear := (-2266610219571762328005792820597000000000000000)
      constant := (63103782225521703054418714942923270209084634445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree098.table
  base := (156065880387616226475582198845119807626649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (11223)
      previous := (0)
      next := (9675)
      square := (443993513116310676291931252200000000000000)
      linear := (-48484333259167947638434980489000000000000000)
      constant := (1359828684840918261191919482272564113253275707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell174.Kernel098
