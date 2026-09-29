import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell076.Parameters
import ForestUnimodality.BinomialMassData.Q10429_20604.Batch000_049
import ForestUnimodality.BinomialMassData.Q10429_20604.Batch050_099
import ForestUnimodality.BinomialMassData.Q10429_20604.Batch100_149
import ForestUnimodality.BinomialMassData.Q10429_20604.Batch150_199
import ForestUnimodality.BinomialMassData.Q5227_10302.Batch000_049
import ForestUnimodality.BinomialMassData.Q5227_10302.Batch050_099
import ForestUnimodality.BinomialMassData.Q5227_10302.Batch100_149
import ForestUnimodality.BinomialMassData.Q5227_10302.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree000.table
  base := (419674407765105522366511077/5000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (42)
      previous := (21)
      next := (21)
      square := (165565683384288585278110162500000000000)
      linear := (-2744565931547774274151807500000000000)
      constant := (209837203882552761183255538500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree000.table
  base := (419674407765105522366511077/5000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (42)
      previous := (21)
      next := (21)
      square := (165565683384288585278110162500000000000)
      linear := (-2744565931547774274151807500000000000)
      constant := (209837203882552761183255538500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree001.table
  base := (231120380608016988144885091393237641360287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-3013264654924742768993570057176567500000000000)
      constant := (2044865244517131937218065834774615229328121424629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree001.table
  base := (461338849278804602761549746581794152842881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-6040743123768026713033265871803760000000000000)
      constant := (4081761060003425404103292070645158099281248613227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (3124659836470982793/6250000000000000000)
  directionHi := (49994557383535724689/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree002.table
  base := (269026156135213578639528346498513343107161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-11955963924108122120228961092455860000000000000)
      constant := (2385439977418980036036458454214489692002341495987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree002.table
  base := (33513118688428481310134658221901712144951/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-2996097887986301117580303151839277500000000000)
      constant := (594330407057427402902793312228194359934178691834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3124659836470982793/6250000000000000000)
  centralHi := (49994557383535724689/100000000000000000000)
  directionLo := (70702981096636179193/100000000000000000000)
  directionHi := (35351490548318089597/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree003.table
  base := (167694942505854981563773658241150975041253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-5961799512788919567490260690186195000000000000)
      constant := (498930659376191844208602119716780049983392515517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree003.table
  base := (41743444789089959288003088869537027468501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-1494003331676865185634096611909205000000000000)
      constant := (124206583218718219554719409430652607647585644589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70702981096636179193/100000000000000000000)
  centralHi := (35351490548318089597/50000000000000000000)
  directionLo := (17318622698040325791/20000000000000000000)
  directionHi := (21648278372550407239/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree004.table
  base := (112615494362962732712641791673695031586907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-23814833152625395284712603048661310000000000000)
      constant := (1020208207484497929836197868424558675928039212169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree004.table
  base := (112096744849645109356572513246936184985523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-23871688408299559984897106078463810000000000000)
      constant := (1015735969796771063106740063870427491973356546641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17318622698040325791/20000000000000000000)
  centralHi := (21648278372550407239/25000000000000000000)
  directionLo := (99989114767071449377/100000000000000000000)
  directionHi := (49994557383535724689/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree005.table
  base := (81116387512052487992517236671043093984809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-29744267766884031866954424026764035000000000000)
      constant := (755176536640467761183824415149536076082744740003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree005.table
  base := (80749595800844037294995137149614320934047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-29815336836476737742185052814017160000000000000)
      constant := (752113200415934831631237712919564113864401058549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99989114767071449377/100000000000000000000)
  centralHi := (49994557383535724689/50000000000000000000)
  directionLo := (27947807203649976417/25000000000000000000)
  directionHi := (111791228814599905669/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree006.table
  base := (61868507547542873750204469732945890934827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-11891234127047556149732081668288920000000000000)
      constant := (200499750973325689284353128761431076160163195603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree006.table
  base := (30801867824753123160586926138992228835209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-5959830877442319249912166591595085000000000000)
      constant := (99902926589176431101655095037506170914562465601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27947807203649976417/25000000000000000000)
  centralHi := (111791228814599905669/100000000000000000000)
  directionLo := (122461155505955759687/100000000000000000000)
  directionHi := (15307644438244469961/12500000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree007.table
  base := (24593723902298271193778186501567152145637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-20801568497700652515719032991484742500000000000)
      constant := (254450973021312418057040483113759214193136513079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree007.table
  base := (48987986520884086869549068317453469552657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-41702633692831093256760946285123860000000000000)
      constant := (507491635825381557662575614633970627300069067419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122461155505955759687/100000000000000000000)
  centralHi := (15307644438244469961/12500000000000000000)
  directionLo := (132273165743583551393/100000000000000000000)
  directionHi := (66136582871791775697/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree008.table
  base := (8037479645874503383178163322780173635117/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-47532571609659941613679886961072210000000000000)
      constant := (451861741380957089938128420300532169676676621195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree008.table
  base := (40029352670818173916485974360475492727377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-47646282121008271014048893020677210000000000000)
      constant := (450925887835694453084345267985516984637480397659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132273165743583551393/100000000000000000000)
  centralHi := (66136582871791775697/50000000000000000000)
  directionLo := (70702981096636179193/50000000000000000000)
  directionHi := (141405962193272358387/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree009.table
  base := (33377218760336621937807935076813796339053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-17820668741306192731973902646391645000000000000)
      constant := (139063532698789717495255410786519441160402419717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree009.table
  base := (8311507681306266112383010406454929264839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-4465827545765454064278069979685880000000000000)
      constant := (34717904240341868549485420076107185336449942671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70702981096636179193/50000000000000000000)
  centralHi := (141405962193272358387/100000000000000000000)
  directionLo := (74991836075303587033/50000000000000000000)
  directionHi := (149983672150607174067/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree010.table
  base := (3495632942762096154204629527488952881371/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-14847860209544303694540882229319415000000000000)
      constant := (99471305005232501463668037190239943291528900114) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree010.table
  base := (5570440473622557982761290330000812634043/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-59533578977362626528624786491783910000000000000)
      constant := (397608537970482126436044821747713085762247907405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74991836075303587033/50000000000000000000)
  centralHi := (149983672150607174067/100000000000000000000)
  directionLo := (15809667194396112417/10000000000000000000)
  directionHi := (158096671943961124171/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree011.table
  base := (1175654686284778762926484430209768530707/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-16330218863108962840101337473845096250000000000)
      constant := (97518310867871969588200041831758836812602033845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree011.table
  base := (23413655097806322014615225027696815165243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-65477227405539804285912733227337260000000000000)
      constant := (390066657795281667140176373335542650871058211881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15809667194396112417/10000000000000000000)
  centralHi := (158096671943961124171/100000000000000000000)
  directionLo := (165813188401080180503/100000000000000000000)
  directionHi := (20726648550135022563/12500000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree012.table
  base := (3953103501535131519640360410264027946621/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-23750103355564829314215723624494370000000000000)
      constant := (130497459147284718929039060222808379425629786345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree012.table
  base := (3935334731811095058661258249448126025583/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-23806958611238994014400226654296870000000000000)
      constant := (130581761633031750903461107989616922033174804435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165813188401080180503/100000000000000000000)
  centralHi := (20726648550135022563/12500000000000000000)
  directionLo := (173186226980403257911/100000000000000000000)
  directionHi := (21648278372550407239/12500000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree013.table
  base := (16562511655424807147683534076226984625099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-77179744680953124524888991851585835000000000000)
      constant := (400729102590003356373438874899324319004270457433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree013.table
  base := (16482577658995221999956834983033246648507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-77364524261894159800488626698443960000000000000)
      constant := (401241007519759682763939065516319095736251059369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173186226980403257911/100000000000000000000)
  centralHi := (21648278372550407239/12500000000000000000)
  directionLo := (180257940140464835499/100000000000000000000)
  directionHi := (360515880280929671/200000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree014.table
  base := (6898380891673830719446702279941432608819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-41554589647605880553565406414844280000000000000)
      constant := (208417150918394568741136831045906450604901790673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree014.table
  base := (6862330016566870572468274253983251867527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-41654086345035668778888286716998655000000000000)
      constant := (208805039944061536576174462573619963044657417709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180257940140464835499/100000000000000000000)
  centralHi := (360515880280929671/200000000000000000)
  directionLo := (187062504932600136089/100000000000000000000)
  directionHi := (18706250493260013609/10000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree015.table
  base := (2847802233405830561782806132417767998999/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-7419884492455866474114386150649273750000000000)
      constant := (36593870432041811502878923001801084773650962911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree015.table
  base := (11326174544993583917248530261513197675977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-29750607039416171771688173389850220000000000000)
      constant := (146724579265844575704107923095864668923373357953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187062504932600136089/100000000000000000000)
  centralHi := (18706250493260013609/10000000000000000000)
  directionLo := (193628088147444911683/100000000000000000000)
  directionHi := (48407022036861227921/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree016.table
  base := (9287396198913381164670355989673328259611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-94968048523729034271614454785894010000000000000)
      constant := (467088524136646014717279867240478517906645000137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree016.table
  base := (369152863277477298268431154672386488707/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-95195469546425693072352466905104010000000000000)
      constant := (468416363907826209191045309166031450832929819225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193628088147444911683/100000000000000000000)
  centralHi := (48407022036861227921/25000000000000000000)
  directionLo := (99989114767071449377/50000000000000000000)
  directionHi := (39995645906828579751/20000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree017.table
  base := (3719577234773516096488839223195954584127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 153015000000000000000000000000000000000000000
      center := (2570652)
      previous := (1285326)
      next := (1285326)
      square := (10133613217218767150532010605975000000000000)
      linear := (-174563119615895624314630234885807500000000000)
      constant := (865592053218237157740905726229660485638038581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree017.table
  base := (7386511295026999436812421266395211945931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306030000000000000000000000000000000000000000
      center := (5141304)
      previous := (2570652)
      next := (2570652)
      square := (20267226434437534301064021211950000000000000)
      linear := (-349962345932881905984914926092240000000000000)
      constant := (1736783139408352616438184100551085171181326393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99989114767071449377/50000000000000000000)
  centralHi := (39995645906828579751/20000000000000000000)
  directionLo := (103066420399160547327/50000000000000000000)
  directionHi := (41226568159664218931/20000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree018.table
  base := (5809011562252770630186669812104947757349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-35608972584082102478699365580699820000000000000)
      constant := (179488693020353601443458361292399710829015256061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree018.table
  base := (1440453550080983478649413139665077240733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-8923563866898337382244030031350892500000000000)
      constant := (45032049299288380359282545768128917897555309237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103066420399160547327/50000000000000000000)
  centralHi := (41226568159664218931/20000000000000000000)
  directionLo := (212108943289908537579/100000000000000000000)
  directionHi := (10605447164495426879/5000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree019.table
  base := (1091504725818289072860834027262755904577/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-28189088091626236004584979430050546250000000000)
      constant := (145319105897456300488574127708532642219655510059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree019.table
  base := (270238072020844562919409665035336427197/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-28256603707739306586054076777941015000000000000)
      constant := (145876420487117357383850436476866544812825318396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212108943289908537579/100000000000000000000)
  centralHi := (10605447164495426879/5000000000000000000)
  directionLo := (217921223361877450881/100000000000000000000)
  directionHi := (108960611680938725441/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree020.table
  base := (1542169711406945064530954631568244103353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-59342893490381790300290869349152455000000000000)
      constant := (314257365201337927095214562842089029571229527251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree020.table
  base := (3046681537709180155617619531641997483367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-118970063259134404101504253847317410000000000000)
      constant := (631065287027101792097241589103127474156225806989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217921223361877450881/100000000000000000000)
  centralHi := (108960611680938725441/50000000000000000000)
  directionLo := (223582457629199811337/100000000000000000000)
  directionHi := (111791228814599905669/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree021.table
  base := (485565756668595082676589690776150582589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-10384601799585184765235296639700636250000000000)
      constant := (56665749135825631291038265072136708026124222421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree021.table
  base := (190874325765748172231259084312713160249/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-20818951947885263643132033430478460000000000000)
      constant := (113811931915150995026902855438642489889426570805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223582457629199811337/100000000000000000000)
  centralHi := (111791228814599905669/50000000000000000000)
  directionLo := (114551921772932922899/50000000000000000000)
  directionHi := (229103843545865845799/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree022.table
  base := (921476931710708130553194303908810004473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-130544656209280853765065380654510360000000000000)
      constant := (735537238127882448869133253248774691831830406291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree022.table
  base := (445852326333611695364160300813886933009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-65428680057744379808040073659212055000000000000)
      constant := (369381418353912935853874064944225943343342709403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114551921772932922899/50000000000000000000)
  centralHi := (229103843545865845799/100000000000000000000)
  directionLo := (1831994217633849737/781250000000000000)
  directionHi := (234495259857132766337/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree023.table
  base := (3249441400359714233084809708045055853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-68237045411769745173653600816306542500000000000)
      constant := (397511273349269012921850822239073574709493844751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree023.table
  base := (-397841482567708385496751487929217407/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-68400504271832968686684047026988730000000000000)
      constant := (399301154897569918706197325494495639353786108275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1831994217633849737/781250000000000000)
  centralHi := (234495259857132766337/100000000000000000000)
  directionLo := (119882737147013652363/50000000000000000000)
  directionHi := (239765474294027304727/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree024.table
  base := (-815777820249628712064302206955940079953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-47467841812599375643183007536905270000000000000)
      constant := (286109665395289746292069839934598849565631440183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree024.table
  base := (-839128205515493922831924733145358126311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-47581552323947705043552013596510270000000000000)
      constant := (287424772131728219904953983949078114306761930321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119882737147013652363/50000000000000000000)
  centralHi := (239765474294027304727/100000000000000000000)
  directionLo := (122461155505955759687/50000000000000000000)
  directionHi := (391875697619058431/160000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree025.table
  base := (-778228741710803642730980599017257944629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-74166480026028381755895421794409267500000000000)
      constant := (462679188571464015146308905662626362817329908057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree025.table
  base := (-788541114008257747295560175336068869287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-74344152700010146443971993762542080000000000000)
      constant := (464840437707600106622695251056523148439637672371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122461155505955759687/50000000000000000000)
  centralHi := (391875697619058431/160000000000000000)
  directionLo := (249972786917678623443/100000000000000000000)
  directionHi := (62493196729419655861/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree026.table
  base := (-2224952225479079674091071828829311200961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-154262394666315400094032664566921260000000000000)
      constant := (996027446278331082387773872766915296812610259413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree026.table
  base := (-1121570295102314775194433353885150533829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-77315976914098735322615967130318755000000000000)
      constant := (500369485298911765105709388962500221343623791657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249972786917678623443/100000000000000000000)
  centralHi := (62493196729419655861/25000000000000000000)
  directionLo := (254923223672082900321/100000000000000000000)
  directionHi := (127461611836041450161/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree027.table
  base := (-113169678869808211624014468805664219979/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-53397276426858012225424828515007995000000000000)
      constant := (356755209000626770677549726613380997509658246725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree027.table
  base := (-2845258164538736825733851779626452763039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-53525200752124882800839960332063620000000000000)
      constant := (358459415642359048660537187336952358000265117529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254923223672082900321/100000000000000000000)
  centralHi := (127461611836041450161/50000000000000000000)
  directionLo := (259779340470604886867/100000000000000000000)
  directionHi := (64944835117651221717/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree028.table
  base := (-3376093431803623392668774990100423233767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-166121263894832673258516306523126710000000000000)
      constant := (1148013072727306554800649350486123180107561236211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree028.table
  base := (-13242881199277481074967746184786818031/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-41629812671137956539951956932936052500000000000)
      constant := (288384767682481718980562065586780943768218990272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259779340470604886867/100000000000000000000)
  centralHi := (64944835117651221717/25000000000000000000)
  directionLo := (264546331487167102787/100000000000000000000)
  directionHi := (66136582871791775697/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree029.table
  base := (-241952816656092021936198011469499114579/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-43012674627272827460189531875307358750000000000)
      constant := (307304757743686012455877557274973043491348925628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree029.table
  base := (-3883614482653629499243828543559874286059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-172462899112729003917095774467297560000000000000)
      constant := (1235170891492623031394807918431444093827659826247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264546331487167102787/100000000000000000000)
  centralHi := (66136582871791775697/25000000000000000000)
  directionLo := (269228930970083055329/100000000000000000000)
  directionHi := (26922893097008305533/10000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree030.table
  base := (-34556508742304531183915580597123299153/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-59326711041116648807666649493110720000000000000)
      constant := (437946819733324501786158008776960958765416422875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree030.table
  base := (-866082827709097213080140525153685187507/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-59468849180302060558127907067616970000000000000)
      constant := (440076952067480484657363143025085086946238379385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269228930970083055329/100000000000000000000)
  centralHi := (26922893097008305533/10000000000000000000)
  directionLo := (273831468314489730747/100000000000000000000)
  directionHi := (68457867078622432687/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree031.table
  base := (-4725176538218735824960356709113003294487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-183909567737608583005241769457434885000000000000)
      constant := (1401840852447351854240442959643040760066677343971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree031.table
  base := (-2367342076232464602302210725095853969359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-92175097984541679715835833969202130000000000000)
      constant := (704341318083968706674879773945666078151979185147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273831468314489730747/100000000000000000000)
  centralHi := (68457867078622432687/25000000000000000000)
  directionLo := (27835791493551075209/10000000000000000000)
  directionHi := (278357914935510752091/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree032.table
  base := (-5091584575608077106431935079374346494377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-189839002351867219587483590435537610000000000000)
      constant := (1493189249831791786683326217574641406653215813341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree032.table
  base := (-5099906803560833404732678393738401926383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-190293844397260537188959614673957610000000000000)
      constant := (1500495433182549730807539691310162765209754403739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27835791493551075209/10000000000000000000)
  centralHi := (278357914935510752091/100000000000000000000)
  directionLo := (70702981096636179193/25000000000000000000)
  directionHi := (282811924386544716773/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree033.table
  base := (-5421756754653559121900202860782624692033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-65256145655375285389908470471213445000000000000)
      constant := (529286464095010872897556724085810075879289125063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree033.table
  base := (-5429034275883823073100172775622364068257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-65412497608479238315415853803170320000000000000)
      constant := (531881045780767180856807301842633837836376289127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70702981096636179193/25000000000000000000)
  centralHi := (282811924386544716773/100000000000000000000)
  directionLo := (143598433437830662081/50000000000000000000)
  directionHi := (287196866875661324163/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree034.table
  base := (-1143642250082706003463510715395106461773/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306030000000000000000000000000000000000000000
      center := (5141304)
      previous := (2570652)
      next := (2570652)
      square := (20267226434437534301064021211950000000000000)
      linear := (-697916510658769871114073468483540000000000000)
      constant := (5833318368147078126943657045257040284751804405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree034.table
  base := (-228982774661712618813438266809184854583/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306030000000000000000000000000000000000000000
      center := (5141304)
      previous := (2570652)
      next := (2570652)
      square := (20267226434437534301064021211950000000000000)
      linear := (-699588724060951185825382381124790000000000000)
      constant := (5861950218828078741538042443051122897379911275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143598433437830662081/50000000000000000000)
  centralHi := (287196866875661324163/100000000000000000000)
  directionLo := (291515859107479741187/100000000000000000000)
  directionHi := (72878964776869935297/25000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree035.table
  base := (-5983083839211319112401688814285663620411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-207627306194643129334209053369845785000000000000)
      constant := (1787079208784154863832954641584355636043898466263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree035.table
  base := (-748579237330080730213941361927759917901/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-52031197420448017615205863720154415000000000000)
      constant := (448964523727385282160891283031973178773370952866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291515859107479741187/100000000000000000000)
  centralHi := (72878964776869935297/25000000000000000000)
  directionLo := (59154358040349867569/20000000000000000000)
  directionHi := (147885895100874668923/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree036.table
  base := (-6218185971113982315237951716182523143739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-71185580269633921972150291449316170000000000000)
      constant := (630531324168643421258783068408393201527697635229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree036.table
  base := (-1244605343151626448438835489561967574957/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-71356146036656416072703800538723670000000000000)
      constant := (633630224298020222877027728514647762869562964135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59154358040349867569/20000000000000000000)
  centralHi := (147885895100874668923/50000000000000000000)
  directionLo := (74991836075303587033/25000000000000000000)
  directionHi := (299967344301214348133/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree037.table
  base := (-6425054021483743982983743939293644056731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-219486175423160402498692695326051235000000000000)
      constant := (1999359711445916044588297155724300324934307888823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree037.table
  base := (-3214636423202752796421036203475622654471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-110006043269073212987699674175862180000000000000)
      constant := (1004593929717773140884776997254649481502609732243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74991836075303587033/25000000000000000000)
  centralHi := (299967344301214348133/100000000000000000000)
  directionLo := (304105020371415306407/100000000000000000000)
  directionHi := (38013127546426913301/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree038.table
  base := (-6604991062404934502689477538747926115327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-225415610037419039080934516304153960000000000000)
      constant := (2110364900886678141809511306406139088239775219691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree038.table
  base := (-3304332591880977249286018475109223509031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-112977867483161801866343647543638855000000000000)
      constant := (1060369109920759372596867839870013063123452924723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304105020371415306407/100000000000000000000)
  centralHi := (38013127546426913301/12500000000000000000)
  directionLo := (308187149607303654283/100000000000000000000)
  directionHi := (77046787401825913571/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree039.table
  base := (-6759102290501914500531144071527348159827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-77115014883892558554392112427418895000000000000)
      constant := (741533255391394403785934666317000519815843779397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree039.table
  base := (-1690574955149832405207581747756752542539/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-19324948616208398457497936818569255000000000000)
      constant := (186294338331237253464139245648962385028618742029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308187149607303654283/100000000000000000000)
  centralHi := (77046787401825913571/25000000000000000000)
  directionLo := (156107955395497230403/50000000000000000000)
  directionHi := (312215910790994460807/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree040.table
  base := (-6888325074745904277574924101724845885047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-237274479265936312245418158260359410000000000000)
      constant := (2342056016966972265574725547779839202458793024451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree040.table
  base := (-6891106005459964038959655530256808490139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-237843031822677959247263188558384410000000000000)
      constant := (2353561161313313416340720660367713607145343816887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156107955395497230403/50000000000000000000)
  centralHi := (312215910790994460807/100000000000000000000)
  directionLo := (316193343887922248341/100000000000000000000)
  directionHi := (158096671943961124171/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree041.table
  base := (-3496727220680285872157235399254173745081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-121601956940097474413829989619231067500000000000)
      constant := (1231363310920425591870268991229567346221613699373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree041.table
  base := (-6995871538953616155321934274653853152501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-243786680250855137004551135293937760000000000000)
      constant := (2474818556337982403390902639715633662640489438233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316193343887922248341/100000000000000000000)
  centralHi := (158096671943961124171/50000000000000000000)
  directionLo := (80030340530561245501/25000000000000000000)
  directionHi := (64024272424448996401/20000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree042.table
  base := (-7075164688777091512696746019555814689233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-83044449498151195136633933405521620000000000000)
      constant := (862201872373485658821186994160256045328633774263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree042.table
  base := (-3538632152160007797044750799798925794363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-41621721446505385793639847004915185000000000000)
      constant := (433216389685192834819371178537517404653822177693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80030340530561245501/25000000000000000000)
  centralHi := (64024272424448996401/20000000000000000000)
  directionLo := (40500220341795894731/12500000000000000000)
  directionHi := (324001762734367157849/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree043.table
  base := (-71340277203254643133774207607192195023/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-63765695777178055498035905298666896250000000000)
      constant := (678421986185010232042920177123317200016262921475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree043.table
  base := (-3567925260353991868462155459921673919979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-127836988553604746259563514382522230000000000000)
      constant := (1363497749419752271940983367577237488014769089607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40500220341795894731/12500000000000000000)
  centralHi := (324001762734367157849/100000000000000000000)
  directionLo := (327836236592224193347/100000000000000000000)
  directionHi := (81959059148056048337/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree044.table
  base := (-7170528593089710463691555875797439638881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-260992217722970858574385442172770310000000000000)
      constant := (2843969314725241721744961153844391445917352854773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree044.table
  base := (-7172110218034046118466634596062656437357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-261617625535386670276414975500597810000000000000)
      constant := (2857905793010275268747445313793239057738745917681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327836236592224193347/100000000000000000000)
  centralHi := (81959059148056048337/25000000000000000000)
  directionLo := (331626376802160361007/100000000000000000000)
  directionHi := (20726648550135022563/6250000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree045.table
  base := (-3592539352829674591816919915182733397967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-44486942056204915859437877191812172500000000000)
      constant := (496241014759515037633356259193795089742020864937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree045.table
  base := (-718645035634125605933504825451805460777/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-44593545660593974672283820372691860000000000000)
      constant := (498670936893365014741645919857173480204716974235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331626376802160361007/100000000000000000000)
  centralHi := (20726648550135022563/6250000000000000000)
  directionLo := (167686843221899858503/50000000000000000000)
  directionHi := (335373686443799717007/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree046.table
  base := (-287121079332540841435793103020776011189/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-272851086951488131738869084128975760000000000000)
      constant := (3114115180247254671670244406082740232746237413425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree046.table
  base := (-897401993525088341930841962223392388467/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-68376230597935256447747717242926127500000000000)
      constant := (782337983126487974614891951941452223141260262622) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167686843221899858503/50000000000000000000)
  centralHi := (335373686443799717007/100000000000000000000)
  directionLo := (169539792767715550637/50000000000000000000)
  directionHi := (13563183421417244051/4000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree047.table
  base := (-223427167647766936486088580777613182107/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-69695130391436692080277726276769621250000000000)
      constant := (813493493108766523635736381527833759751558555448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree047.table
  base := (-1430139897624275477868296373847109978749/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-279448570819918203548278815707257860000000000000)
      constant := (3269882139548027252458042563499837493347897590085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169539792767715550637/50000000000000000000)
  centralHi := (13563183421417244051/4000000000000000000)
  directionLo := (342745417321450678743/100000000000000000000)
  directionHi := (42843177165181334843/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree048.table
  base := (-887532106015344588672717612802301946877/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-23725829681667117075279393840431767500000000000)
      constant := (283085020435438744110107222426316538911466663894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree048.table
  base := (-1420229789333097146595700228627486116423/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-95130739749365127101855587480937070000000000000)
      constant := (1137871349789518585629534467102936075412603171765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342745417321450678743/100000000000000000000)
  centralHi := (42843177165181334843/12500000000000000000)
  directionLo := (346372453960806515823/100000000000000000000)
  directionHi := (21648278372550407239/6250000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree049.table
  base := (-3515001157794049699731461621453658120629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-145319695397132020742797273531641967500000000000)
      constant := (1771626057915895295970804103050501044141938916057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree049.table
  base := (-3515387273870602495208241183173394377513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-145667933838136279531427354589182280000000000000)
      constant := (1780272901345581872137712226680611069078976232029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346372453960806515823/100000000000000000000)
  centralHi := (21648278372550407239/6250000000000000000)
  directionLo := (349961901684750072821/100000000000000000000)
  directionHi := (174980950842375036411/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree050.table
  base := (-6939086321140644965713082080738350780757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-296568825408522678067836368041386660000000000000)
      constant := (3692667987386716993449426772846431531055326629881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree050.table
  base := (-6939754514290122050983743461391165707809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-297279516104449736820142655913917910000000000000)
      constant := (3710675823264570294765586625289360339038893218997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349961901684750072821/100000000000000000000)
  centralHi := (174980950842375036411/50000000000000000000)
  directionLo := (70702981096636179193/20000000000000000000)
  directionHi := (176757452741590447983/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree051.table
  base := (-1365532399969882172900201155058570433017/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6755742144812511433688007070650000000000000)
      linear := (-348902260695249497866295489065155000000000000)
      constant := (4435140144778093056554735818495070740063967915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree051.table
  base := (-3414119969697098862955462329991006984259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3377871072406255716844003535325000000000000)
      linear := (-174869183698170077610974972692890000000000000)
      constant := (2228375302641993479850651405019045487753573941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70702981096636179193/20000000000000000000)
  centralHi := (176757452741590447983/50000000000000000000)
  directionLo := (357032553371198868821/100000000000000000000)
  directionHi := (178516276685599434411/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree052.table
  base := (-1673964807876934774753038631401061645579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-77106923659259987808080002499398027500000000000)
      constant := (1000261630386972357548427172737315431723039954407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree052.table
  base := (-837044864490712551898948932375143404343/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-77291703240201023083679637346256152500000000000)
      constant := (1005131381088384950884136823716451330137403096838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (357032553371198868821/100000000000000000000)
  centralHi := (178516276685599434411/50000000000000000000)
  directionLo := (360515880280929670999/100000000000000000000)
  directionHi := (360515880280929671/100000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree053.table
  base := (-6543788172045099540472017659636212533101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-314357129251298587814561830975694835000000000000)
      constant := (4160007061214113379222111136966376377863508418033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree053.table
  base := (-6544220037600398743466037467958092508933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-315110461388981270092006496120577960000000000000)
      constant := (4180243111549722843365598365336805677540296662889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360515880280929670999/100000000000000000000)
  centralHi := (360515880280929671/100000000000000000)
  directionLo := (90991467904520195473/25000000000000000000)
  directionHi := (363965871618080781893/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree054.table
  base := (-6371542248688119907164918617773020222421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-106762187955185741465601217317932520000000000000)
      constant := (1440715766075313720689351984755151072085503096531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree054.table
  base := (-3185957683557719598947995994784771122601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-53509018302859741308215740476021885000000000000)
      constant := (723859120357115251646268723596845948885942340511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90991467904520195473/25000000000000000000)
  centralHi := (363965871618080781893/100000000000000000000)
  directionLo := (183691733258933639531/50000000000000000000)
  directionHi := (367383466517867279063/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree055.table
  base := (-193100021884398511918568468322043870429/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-81553999619953965244761368232975071250000000000)
      constant := (1121866632943425802239004946404817362287450155656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree055.table
  base := (-3089761476244661458200758673260115286561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-163498879122667812803291194795842330000000000000)
      constant := (2254629832927465679034510183880075711204873004213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183691733258933639531/50000000000000000000)
  centralHi := (367383466517867279063/100000000000000000000)
  directionLo := (14830782433231797877/4000000000000000000)
  directionHi := (185384780415397473463/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree056.table
  base := (-5966830731968383210844390058001576746841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-332145433094074497561287293910003010000000000000)
      constant := (4655964167477680606113352292242319828829946789453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree056.table
  base := (-1193421792074843342332114632818978302313/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-332941406673512803363870336327238010000000000000)
      constant := (4678557357490904128519959583932794726135685552145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14830782433231797877/4000000000000000000)
  centralHi := (185384780415397473463/50000000000000000000)
  directionLo := (187062504932600136089/50000000000000000000)
  directionHi := (374125009865200272179/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree057.table
  base := (-1146897868480643538214276575029593762799/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-112691622569444378047843038296035245000000000000)
      constant := (1609213233742014651249114490865374292892118294445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree057.table
  base := (-5734729484643056565882739589764424302739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-112961685033896660373719427687597120000000000000)
      constant := (1617015766980473503776620404438957865621762484229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187062504932600136089/50000000000000000000)
  centralHi := (374125009865200272179/100000000000000000000)
  directionLo := (188725315455168763791/50000000000000000000)
  directionHi := (377450630910337527583/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree058.table
  base := (-1096444974770662584487949530705478694653/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-344004302322591770725770935866208460000000000000)
      constant := (5002492705467044054631123199597911782808386978245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree058.table
  base := (-5482432079679458266647706637950862956327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-344828703529867158878446229798344710000000000000)
      constant := (5026729075622814788047955193647605715133834672691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188725315455168763791/50000000000000000000)
  centralHi := (377450630910337527583/100000000000000000000)
  directionLo := (95186801390275313563/25000000000000000000)
  directionHi := (380747205561101254253/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree059.table
  base := (-5210078326653363535188847925665122376877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-349933736936850407308012756844311185000000000000)
      constant := (5180522817582773780091388268255969854486225185841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree059.table
  base := (-2605128530137407034598742375166371035591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-175386175979022168317867088266949030000000000000)
      constant := (2602801162490153918133574517480999096390166693203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95186801390275313563/25000000000000000000)
  centralHi := (380747205561101254253/100000000000000000000)
  directionLo := (192007740931559280401/50000000000000000000)
  directionHi := (384015481863118560803/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree060.table
  base := (-983616894831334048760396871990813028337/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-118621057183703014630084859274137970000000000000)
      constant := (1787243243342804017759319200139250580050515010035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree060.table
  base := (-1229559650914629045261573749597090575373/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-29726333365518459532751843605787617500000000000)
      constant := (448972228895113132588038963317239237842739187803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (192007740931559280401/50000000000000000000)
  centralHi := (384015481863118560803/100000000000000000000)
  directionLo := (387256176294889823367/100000000000000000000)
  directionHi := (48407022036861227921/12500000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree061.table
  base := (-1151568202090170232471431504329964737871/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-90448151541341920118124099700129158750000000000)
      constant := (1386528295492214770451829577588622959351433864443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree061.table
  base := (-921281136755938754545641262517748344793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-362659648814398692150310070005004760000000000000)
      constant := (5572922084652621909614218929964733579499213241345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387256176294889823367/100000000000000000000)
  centralHi := (48407022036861227921/12500000000000000000)
  directionLo := (78093995120371305847/20000000000000000000)
  directionHi := (97617493900464132309/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree062.table
  base := (-2137334170967773644435892304519529123761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-183861020389813158527369109889309680000000000000)
      constant := (2866836476092690830577284829712316693965181671813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree062.table
  base := (-4274782863374399107086480742960635282033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-368603297242575869907598016740558110000000000000)
      constant := (5761368121474704895201863156714182391076079845189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78093995120371305847/20000000000000000000)
  centralHi := (97617493900464132309/25000000000000000000)
  directionLo := (19682876924784781043/5000000000000000000)
  directionHi := (393657538495695620861/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree063.table
  base := (-1961646144230574594136723775299426268627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-62275245898980825606163340126120347500000000000)
      constant := (987401475509902551323916584612977958773649696197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree063.table
  base := (-1961695482732771659077531580518683803059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-62424490945125507944147660579351910000000000000)
      constant := (992167445507205362438788540758015977735723595749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19682876924784781043/5000000000000000000)
  centralHi := (393657538495695620861/100000000000000000000)
  directionLo := (396819497230750654181/100000000000000000000)
  directionHi := (198409748615375327091/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree064.table
  base := (-1776081319683434004957953766185238388623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-189790455004071795109610930867412405000000000000)
      constant := (3059160362734977430794208451817051700232368425659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree064.table
  base := (-222015477665490415528408472724662401313/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-95122648524732556355543477552916202500000000000)
      constant := (1536957895808485699822916603322899232951706709716) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396819497230750654181/100000000000000000000)
  centralHi := (198409748615375327091/50000000000000000000)
  directionLo := (399956459068285797509/100000000000000000000)
  directionHi := (39995645906828579751/10000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree065.table
  base := (-3161294653260020173206227506853748631947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-385510344622402226801463682712927535000000000000)
      constant := (6315408434465803167522601800855623626523176002151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree065.table
  base := (-3161367859716582366547994438977579676317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-386434242527107403179461856947218160000000000000)
      constant := (6345848719694191772053533931254997790828878875361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399956459068285797509/100000000000000000000)
  centralHi := (39995645906828579751/10000000000000000000)
  directionLo := (403069007638167361733/100000000000000000000)
  directionHi := (201534503819083680867/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree066.table
  base := (-2750701270946942836743535434110096516113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-130479926412220287794568501230343420000000000000)
      constant := (2171890621865004594874460721898826607171908941943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree066.table
  base := (-171922768926913472000853291352882268139/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-32698157579607048411395816973564292500000000000)
      constant := (545587997518683573811463986366144870668017454516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (403069007638167361733/100000000000000000000)
  centralHi := (201534503819083680867/50000000000000000000)
  directionLo := (406157704206620541411/100000000000000000000)
  directionHi := (101539426051655135353/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree067.table
  base := (-145024591714406197610154162775914506251/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-99342303462729874991486831167283246250000000000)
      constant := (1679777730447932766332083708500464098593921947932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree067.table
  base := (-1160223863196222589570254713964357620461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-199160769691730879347018875209162430000000000000)
      constant := (3375726619854584506973965042326352083971158252913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406157704206620541411/100000000000000000000)
  centralHi := (101539426051655135353/25000000000000000000)
  directionLo := (81844617771572080789/20000000000000000000)
  directionHi := (204611544428930201973/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree068.table
  base := (-1870380550454317367327954152869534122743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306030000000000000000000000000000000000000000
      center := (5141304)
      previous := (2570652)
      next := (2570652)
      square := (20267226434437534301064021211950000000000000)
      linear := (-1395497053512727116083699465907390000000000000)
      constant := (23964448168635934927748494971583953647241695971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree068.table
  base := (-187042724712577973846375692144769266673/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 153015000000000000000000000000000000000000000
      center := (2570652)
      previous := (1285326)
      next := (1285326)
      square := (10133613217218767150532010605975000000000000)
      linear := (-699420740158544872753158645594945000000000000)
      constant := (12039862365948705040768443708414578130660030905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81844617771572080789/20000000000000000000)
  centralHi := (204611544428930201973/50000000000000000000)
  directionLo := (103066420399160547327/25000000000000000000)
  directionHi := (412265681596642189309/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree069.table
  base := (-700335206855406502027773062352478330573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-68204680513239462188405161104223072500000000000)
      constant := (1189252598768875471998621147131809148573399375003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree069.table
  base := (-43772206043377947581616996568139493781/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-34184069686651342850717803657452630000000000000)
      constant := (597484793775007783618433677060856371038349323928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103066420399160547327/25000000000000000000)
  centralHi := (412265681596642189309/100000000000000000000)
  directionLo := (12977686980565777579/3125000000000000000)
  directionHi := (415285983378104882529/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree070.table
  base := (-911269751597457909304569479025379861023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-415157517693695409712672787603441160000000000000)
      constant := (7348481078217095333890983879444515153232689694859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree070.table
  base := (-227826079133048183706447095486828727433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-104038121166998322991475397656246227500000000000)
      constant := (1845946103778120318871144846551453416751312323389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12977686980565777579/3125000000000000000)
  centralHi := (415285983378104882529/100000000000000000000)
  directionLo := (83656895414136724041/20000000000000000000)
  directionHi := (209142238535341810103/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree071.table
  base := (-100546060340085538761068160871975104583/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-105271738076988511573728652145385971250000000000)
      constant := (1891155481834058113628635196966303460451465024339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree071.table
  base := (-100553492523399197739776116109904844927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-105524033274042617430797384340134565000000000000)
      constant := (1900235266959641045207638897466854805831872016491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83656895414136724041/20000000000000000000)
  centralHi := (209142238535341810103/50000000000000000000)
  directionLo := (210630814178665996101/50000000000000000000)
  directionHi := (421261628357331992203/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree072.table
  base := (126581302422594596323327941043715680909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-142338795640737560959052143186548870000000000000)
      constant := (2594646032463083801059408104437187366718015332901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree072.table
  base := (31638934574684785437844387970675419593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-35669981793695637290039790341340967500000000000)
      constant := (651773953486901225842039439315749390527072507777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210630814178665996101/50000000000000000000)
  centralHi := (421261628357331992203/100000000000000000000)
  directionLo := (212108943289908537579/50000000000000000000)
  directionHi := (424217886579817075159/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree073.table
  base := (337511398409157157871186228033980027677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-216472910768235659729699125268874667500000000000)
      constant := (4003214776132801124215955336817080524124942777759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree073.table
  base := (168750204534092079427198949630221698747/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-108495857488131206309441357707911240000000000000)
      constant := (2011205875458027673633248177810853030097912033449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212108943289908537579/50000000000000000000)
  centralHi := (424217886579817075159/100000000000000000000)
  directionLo := (213576842765210731637/50000000000000000000)
  directionHi := (17086147421216858531/4000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree074.table
  base := (621568389706449312702006604889531532757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-219437628075364978020820035757926030000000000000)
      constant := (4116048130671385915813025772442173373630622154119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree074.table
  base := (621558943424965783752699318216562508203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-219963539190351001497526688783599155000000000000)
      constant := (4135774608945052787801486760432652062644737022201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213576842765210731637/50000000000000000000)
  centralHi := (17086147421216858531/4000000000000000000)
  directionLo := (53758680524375235109/12500000000000000000)
  directionHi := (430069444195001880873/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree075.table
  base := (457730078515423645635441916488683998471/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-37067057563749049385323491041162898750000000000)
      constant := (705078183221059407626040369738411008701618371919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree075.table
  base := (114431504828010408315002034910389810133/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-37155893900739931729361777025229305000000000000)
      constant := (708455380388216190746026623835858666614860743348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53758680524375235109/12500000000000000000)
  centralHi := (430069444195001880873/100000000000000000000)
  directionLo := (432965567451008144779/100000000000000000000)
  directionHi := (21648278372550407239/5000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree076.table
  base := (609592727738169503898068967182715329967/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-112683531344811807301530928368014377500000000000)
      constant := (2173238835543715776626862296674286662163221249189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree076.table
  base := (2438356959047382538055047967112163321123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-451814375237056358509629271038305010000000000000)
      constant := (8734569520643498988494797392902954651359618551841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432965567451008144779/100000000000000000000)
  centralHi := (21648278372550407239/5000000000000000000)
  directionLo := (217921223361877450881/50000000000000000000)
  directionHi := (435842446723754901763/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree077.table
  base := (191592903675592454079428810024136898249/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-114165889998376466447091383612540058750000000000)
      constant := (2232036918309132638138383270813645661284413953932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree077.table
  base := (306547447234654096649079547410001264781/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-228879011832616768133458608886929180000000000000)
      constant := (4485432033813252447566332607184827464530304302635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217921223361877450881/50000000000000000000)
  centralHi := (435842446723754901763/100000000000000000000)
  directionLo := (27418778787747365821/6250000000000000000)
  directionHi := (438700460603957853137/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree078.table
  base := (464033145923822186384654464299068687609/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-38549416217313708530883946285688580000000000000)
      constant := (763876264667028435404273931060427953591369058402) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree078.table
  base := (1856127435614782908939564264058866545269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-77283612015568452337367527418235285000000000000)
      constant := (1535058031694377345520915089555764569814575540941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27418778787747365821/6250000000000000000)
  centralHi := (438700460603957853137/100000000000000000000)
  directionLo := (110384993857323181103/25000000000000000000)
  directionHi := (441539975429292724413/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree079.table
  base := (2189352759360555337034837391373411649483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-234261214611011569476424588203182842500000000000)
      constant := (4704028918526460072208515889345198786516438063961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree079.table
  base := (1094674168988324452455315939233175613133/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-117411330130396972945373277811241265000000000000)
      constant := (2363255468793883232589052530294641606005436958511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110384993857323181103/25000000000000000000)
  centralHi := (441539975429292724413/100000000000000000000)
  directionLo := (444361345832506080773/100000000000000000000)
  directionHi := (222180672916253040387/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree080.table
  base := (1266201556432794971618750335159527300221/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-118612965959070443883772749346117102500000000000)
      constant := (2413193911249769369367631802468382297036943683007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree080.table
  base := (5064798632414162479047770381923380680349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-475588968949765069538781057980518410000000000000)
      constant := (9698885111562684608617287427157445152279648209183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444361345832506080773/100000000000000000000)
  centralHi := (222180672916253040387/50000000000000000000)
  directionLo := (17886596610335984907/4000000000000000000)
  directionHi := (111791228814599905669/25000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree081.table
  base := (5770566197175903413547000952610079634063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-160127099483513470705777606120857045000000000000)
      constant := (3300222863397184042581046702856033420183305155607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree081.table
  base := (5770559677785561251579748614482329134967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-160510872459314082432023001572023920000000000000)
      constant := (3315979296642598965139544604391511952717175728063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17886596610335984907/4000000000000000000)
  centralHi := (111791228814599905669/25000000000000000000)
  directionLo := (224975508225910761099/50000000000000000000)
  directionHi := (449951016451821522199/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree082.table
  base := (3247992253941636900058865534446725652529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-243155366532399524349787319670336930000000000000)
      constant := (5075868332223937920187687330511645230196715701243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree082.table
  base := (6495978911386651308018957001836573424299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-487476265806119425053356951451625110000000000000)
      constant := (10200180202305007935080458452491046465729604643833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224975508225910761099/50000000000000000000)
  centralHi := (449951016451821522199/100000000000000000000)
  directionLo := (22635998595931382533/5000000000000000000)
  directionHi := (452719971918627650661/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree083.table
  base := (7241060373520732386235053893825163593323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-492240167679057685281816460318776585000000000000)
      constant := (10405979860831202049785451953353464237513028029241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree083.table
  base := (11585688911977863339902037745772697257/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-493419914234296602810644898187178460000000000000)
      constant := (10455612041944096610123354033147660952406922261875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22635998595931382533/5000000000000000000)
  centralHi := (452719971918627650661/100000000000000000000)
  directionLo := (113868023590355101671/25000000000000000000)
  directionHi := (91094418872284081337/20000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree084.table
  base := (250181035287319993873640815504029717611/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-41514133524443026822004856774739942500000000000)
      constant := (888616514455085862091231466601592070729296763032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree084.table
  base := (200144725171653404318320748767468705123/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-41613630221872815047327737076894317500000000000)
      constant := (892852783593776380426983247111246525474173599470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113868023590355101671/25000000000000000000)
  centralHi := (91094418872284081337/20000000000000000000)
  directionLo := (114551921772932922899/25000000000000000000)
  directionHi := (458207687091731691597/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree085.table
  base := (8790182211297827592273719823232608119113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306030000000000000000000000000000000000000000
      center := (5141304)
      previous := (2570652)
      next := (2570652)
      square := (20267226434437534301064021211950000000000000)
      linear := (-1744287324939705738568512464619315000000000000)
      constant := (37799278883573283939240880637016771881269215139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree085.table
  base := (4395089337036590245097277624490913271797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 153015000000000000000000000000000000000000000
      center := (2570652)
      previous := (1285326)
      next := (1285326)
      square := (10133613217218767150532010605975000000000000)
      linear := (-874233929222579512673392373111220000000000000)
      constant := (18989695987893463243103778818276151668856803591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114551921772932922899/25000000000000000000)
  centralHi := (458207687091731691597/100000000000000000000)
  directionLo := (230463522210093992521/50000000000000000000)
  directionHi := (460927044420187985043/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree086.table
  base := (2398556785529999668791761473927913363303/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-127507117880458398757135480813271190000000000000)
      constant := (2796940032070285040178231398350132472662919733901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree086.table
  base := (1199278013421509859034800941583062857749/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-127812714879707034020627184598459627500000000000)
      constant := (2810261167867397988398688150084752786183430349966) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230463522210093992521/50000000000000000000)
  centralHi := (460927044420187985043/100000000000000000000)
  directionLo := (231815226013039097333/50000000000000000000)
  directionHi := (463630452026078194667/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree087.table
  base := (5208963758394152926462478916929438215533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-85992984356015371935130624038531247500000000000)
      constant := (1909117293777602271322343300660508774641892466437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree087.table
  base := (325560153546572037349148605629300729873/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-43099542328917109486649723760782655000000000000)
      constant := (959102880920718328130219930788570318350444501576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231815226013039097333/50000000000000000000)
  centralHi := (463630452026078194667/100000000000000000000)
  directionLo := (46631818730763787443/10000000000000000000)
  directionHi := (466318187307637874431/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree088.table
  base := (2815320748049253927220456685713570608321/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-130471835187587717048256391302322552500000000000)
      constant := (2931205624367895186134051016029178098983343345707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree088.table
  base := (11261280759304736190612061392405722548321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-523138156375182491597084631864945210000000000000)
      constant := (11780613976793275860359190824679912262545271325707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46631818730763787443/10000000000000000000)
  centralHi := (466318187307637874431/100000000000000000000)
  directionLo := (1831994217633849737/390625000000000000)
  directionHi := (468990519714265532673/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree089.table
  base := (242485865552333779718056005490240113261/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-263908387682304752387633693093696467500000000000)
      constant := (5999058165063876362484488042344288186082263117175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree089.table
  base := (6062145681337440525002684109502024009439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-264540902401679834677186289300249280000000000000)
      constant := (6027591443104116944881091622698546813629889036213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1831994217633849737/390625000000000000)
  centralHi := (468990519714265532673/100000000000000000000)
  directionLo := (235823855530898598327/50000000000000000000)
  directionHi := (94329542212359439331/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree090.table
  base := (13006958126730243610115012744350091631199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-177915403326289380452503069055165220000000000000)
      constant := (4091528419485211842903376839169982804786929828711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree090.table
  base := (1625869560583996499076580769857873243233/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-44585454435961403925971710444670992500000000000)
      constant := (1027745108098362017461479512612516505343539063474) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235823855530898598327/50000000000000000000)
  centralHi := (94329542212359439331/20000000000000000000)
  directionLo := (14821562994746355391/3125000000000000000)
  directionHi := (474290015831883372513/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree091.table
  base := (111274218647030852639934957380058004311/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-539675644593126777939751028143598385000000000000)
      constant := (12554229280609794813228424753400209152576704379625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree091.table
  base := (6954637961495706806402670832028690030559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-270484550829857012434474236035802630000000000000)
      constant := (6306944603960185481295775656068789097540501955253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14821562994746355391/3125000000000000000)
  centralHi := (474290015831883372513/100000000000000000000)
  directionLo := (119229420364109332367/25000000000000000000)
  directionHi := (476917681456437329469/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree092.table
  base := (14831250713333960524584739504178336429251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-545605079207385414521992849121701110000000000000)
      constant := (12837048395027195942167701051604036742996122454017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree092.table
  base := (57934568384251706546934715539791251133/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-136728187521972800656559104701789652500000000000)
      constant := (3224506654228400700972130406047422233754195488704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119229420364109332367/25000000000000000000)
  centralHi := (476917681456437329469/100000000000000000000)
  directionLo := (119882737147013652363/25000000000000000000)
  directionHi := (479530948588054609453/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree093.table
  base := (7886439062219747173266923323371225830307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-91922418970274008517372445016633972500000000000)
      constant := (2187173766730706792169099426953368122849343933323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree093.table
  base := (3154575417968845537394332672310973585249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-184285466172022793461174788514237320000000000000)
      constant := (4395117840959328425855575507985832726529815695805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119882737147013652363/25000000000000000000)
  centralHi := (479530948588054609453/100000000000000000000)
  directionLo := (120532512839310062099/25000000000000000000)
  directionHi := (482130051357240248397/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree094.table
  base := (836707971874611682816039832588393406969/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-139365987108975671921619122769476640000000000000)
      constant := (3353052973890083024876824650458869300086367483615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree094.table
  base := (16734158550753049523512099962936025445537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-558800046944245558140812312278265310000000000000)
      constant := (13475869924728629858072510591586303652959123186379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120532512839310062099/25000000000000000000)
  centralHi := (482130051357240248397/100000000000000000000)
  directionLo := (96943043523444376319/20000000000000000000)
  directionHi := (121178804404305470399/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree095.table
  base := (1771509454524809912427363195638811375217/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-281696691525080662134359156028004642500000000000)
      constant := (6852278139803487354942503678425590884012781654695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree095.table
  base := (8857546892660295071407727582357530837831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-282371847686211367949050129506909330000000000000)
      constant := (6884787910773864410094497407798126623440511064877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96943043523444376319/20000000000000000000)
  centralHi := (121178804404305470399/25000000000000000000)
  directionLo := (487286669177073232579/100000000000000000000)
  directionHi := (24364333458853661629/5000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree096.table
  base := (18715683356959365167312121588178134839037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-189774272554806653616986711011370670000000000000)
      constant := (4666691917240523823149410193875175209359481750293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree096.table
  base := (18715682705780472530338334512426806099097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-190229114600199971218462735249790670000000000000)
      constant := (4688823737519684297325631510781912550365880775633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487286669177073232579/100000000000000000000)
  centralHi := (24364333458853661629/5000000000000000000)
  directionLo := (489844622023823038749/100000000000000000000)
  directionHi := (391875697619058431/80000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree097.table
  base := (3947185159172426083544293139115197875819/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-575252252278678597433201954012214735000000000000)
      constant := (14298770311225201938539233406419734598232880398365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree097.table
  base := (19735925237930036781415556064135843130313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-576630992228777091412676152484925360000000000000)
      constant := (14366556097106333937129156327136701553414603965571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489844622023823038749/100000000000000000000)
  centralHi := (391875697619058431/80000000000000000)
  directionLo := (492389286534178874257/100000000000000000000)
  directionHi := (246194643267089437129/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree098.table
  base := (20775821797045657773112455915631888538411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-581181686892937234015443774990317460000000000000)
      constant := (14600639957543778227057679334553247838447946639737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree098.table
  base := (4155164263811701933944746443083239332207/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-582574640656954269169964099220478710000000000000)
      constant := (14669830474634941133455724731651111239394702036345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492389286534178874257/100000000000000000000)
  centralHi := (246194643267089437129/50000000000000000000)
  directionLo := (494920867676453254351/100000000000000000000)
  directionHi := (30932554229778328397/6250000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree099.table
  base := (21835371305645578467516866582728227787389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-195703707169065290199228531989473395000000000000)
      constant := (4968561563397355069616961621574363511454495849621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree099.table
  base := (5458842724047715129392409805712125573561/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-49043190757094287243937670496336005000000000000)
      constant := (1248024528723029097109157494250952196445033874929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494920867676453254351/100000000000000000000)
  centralHi := (30932554229778328397/6250000000000000000)
  directionLo := (497439565203240541511/100000000000000000000)
  directionHi := (62179945650405067689/12500000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree100.table
  base := (11457287137655881969376373706330804395183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-296520278060727253589963708473261455000000000000)
      constant := (7606952254380064985715293363017520974395771965861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree100.table
  base := (22914573924599273926870692615443005820859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-594461937513308624684539992691585410000000000000)
      constant := (15285947706834973290984298260106159766762231165353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497439565203240541511/100000000000000000000)
  centralHi := (62179945650405067689/12500000000000000000)
  directionLo := (499945573835357246887/100000000000000000000)
  directionHi := (62493196729419655861/12500000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree101.table
  base := (12006715333454570409130061091653360388887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (72828)
      previous := (36414)
      next := (36414)
      square := (287090894988356406872243021775000000000000)
      linear := (-29358395781575979990303364274317500000000000)
      constant := (760969484016363664192758116031123150957165029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree101.table
  base := (4802686073308297576702630118069984427131/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (145656)
      previous := (72828)
      next := (72828)
      square := (574181789976712813744486043550000000000000)
      linear := (-58857522394028605278093122186760000000000000)
      constant := (1529143276225567186358412902466605882491612885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499945573835357246887/100000000000000000000)
  centralHi := (62493196729419655861/12500000000000000000)
  directionLo := (502439083437525081883/100000000000000000000)
  directionHi := (125609770859381270471/25000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree102.table
  base := (3141492555927007660755436828922649192977/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1688935536203127858422001767662500000000000)
      linear := (-174423133030557030087777121944270000000000000)
      constant := (4567436390520524064314033975971429263835116754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree102.table
  base := (25131940190191449726248754493042961927203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6755742144812511433688007070650000000000000)
      linear := (-699364745524409435062417400418330000000000000)
      constant := (18356197123668954774153823589449591254619397803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502439083437525081883/100000000000000000000)
  centralHi := (125609770859381270471/25000000000000000000)
  directionLo := (504920279186245338409/100000000000000000000)
  directionHi := (50492027918624533841/10000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree103.table
  base := (13135051794495107807901972698916338506607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-305414429982115208463326439940415542500000000000)
      constant := (8078807238391931542427879198808970290602313572069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree103.table
  base := (52540206737466004087025986248827684719/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-153073220699460039489100958224561365000000000000)
      constant := (4058511185732430699592494484327400745705831996625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504920279186245338409/100000000000000000000)
  centralHi := (50492027918624533841/10000000000000000000)
  directionLo := (253694670865142328843/50000000000000000000)
  directionHi := (507389341730284657687/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree104.table
  base := (27427920068176632120040852041094445440193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-616758294578489053508894700858933810000000000000)
      constant := (16478534636070466334223020722574638187689999423531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree104.table
  base := (857122496237242796414462213898552498389/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-154559132806504333928422944908449702500000000000)
      constant := (4139114017675893523156002312843371883674155086904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253694670865142328843/50000000000000000000)
  centralHi := (507389341730284657687/100000000000000000000)
  directionLo := (254923223672082900321/50000000000000000000)
  directionHi := (509846447344165800643/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree105.table
  base := (5721077973047235167360905042468227611011/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-207562576397582563363712173945678845000000000000)
      constant := (5600876626670136341063446303456980626472589039895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree105.table
  base := (7151347425946049406858725591343700173779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-52015014971182876122581643864112680000000000000)
      constant := (1406838074114553504001501035668733617076615958331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254923223672082900321/50000000000000000000)
  centralHi := (509846447344165800643/100000000000000000000)
  directionLo := (256145884037516244469/50000000000000000000)
  directionHi := (512291768075032488939/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree106.table
  base := (14901256481788118151171548160587853391437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-314308581903503163336689171407569630000000000000)
      constant := (8564950104228470837294648806722233263600724341679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree106.table
  base := (14901256412682949863813536648859018037881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-315061914041185845614133836552452755000000000000)
      constant := (8605423599400955125525460854024605780884835678227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256145884037516244469/50000000000000000000)
  centralHi := (512291768075032488939/100000000000000000000)
  directionLo := (514725471883234590797/100000000000000000000)
  directionHi := (257362735941617295399/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree107.table
  base := (31019289349268075787154935673120634928029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-634546598421264963255620163793241985000000000000)
      constant := (17460345621286874812967210641842124547888014259743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree107.table
  base := (31019289230964184058074945768423610245411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-636067476510548868985555619840458860000000000000)
      constant := (17542826998867107045573697797331165960614350408737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514725471883234590797/100000000000000000000)
  centralHi := (257362735941617295399/50000000000000000000)
  directionLo := (258573861388479370081/50000000000000000000)
  directionHi := (517147722776958740163/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree108.table
  base := (4031964876329708507205765800698139560159/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-53373002752960299986488498730945392500000000000)
      constant := (1482830509866413352779097418771280045115539172302) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree108.table
  base := (16127859454690968879097560870497107222189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-107001854156454341123807261096002035000000000000)
      constant := (2979666048245200362636367891311434776333555946821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258573861388479370081/50000000000000000000)
  centralHi := (517147722776958740163/100000000000000000000)
  directionLo := (103911736188241954747/20000000000000000000)
  directionHi := (64944835117651221717/12500000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree109.table
  base := (8377950484479714549766470466769846082529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-161601366912445559105025951437361858750000000000)
      constant := (4532690424925205863526438642019590764896540511243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree109.table
  base := (33511801851261995772041310626650766396747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-647954773366903224500131513311565560000000000000)
      constant := (18216355070531438375666591428034790246267458399449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103911736188241954747/20000000000000000000)
  centralHi := (64944835117651221717/12500000000000000000)
  directionLo := (52195850286143003173/10000000000000000000)
  directionHi := (521958502861430031731/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree110.table
  base := (34787538122959370695443714620173274119921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-652334902264040873002345626727550160000000000000)
      constant := (18470732365126363573916161515294353935080771342907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree110.table
  base := (34787538048802778800698814414861640136489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-653898421795080402257419460047118910000000000000)
      constant := (18557903341978816394777575638400200213425025158563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52195850286143003173/10000000000000000000)
  centralHi := (521958502861430031731/100000000000000000000)
  directionLo := (20973893657681059543/4000000000000000000)
  directionHi := (2048231802507915971/390625000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree111.table
  base := (18041463779485815973041331665835300258163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-109710722813049918264097907950942147500000000000)
      constant := (3135646352435591579928945759130645023565287500507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree111.table
  base := (18041463747758693777988089045147847840397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-109973678370542930002451234463778710000000000000)
      constant := (3150440183959327393974047467281793477341948151333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20973893657681059543/4000000000000000000)
  centralHi := (2048231802507915971/390625000000000000)
  directionLo := (131681336530014940533/25000000000000000000)
  directionHi := (526725346120059762133/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree112.table
  base := (4674746280040199229597608676261296094843/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-166048442873139536541707317170938902500000000000)
      constant := (4790049737028138036316361489316902458857697630162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree112.table
  base := (3739797018602953031184027525831749211177/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-332892859325717378885997676759112805000000000000)
      constant := (9625284177907666461685895551613784495503443861295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131681336530014940533/25000000000000000000)
  centralHi := (526725346120059762133/100000000000000000000)
  directionLo := (21163706518973368223/4000000000000000000)
  directionHi := (66136582871791775697/12500000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree113.table
  base := (38732666162349780066086334075896298936243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-670123206106816782749071089661858335000000000000)
      constant := (19509694865582161918501261757855680021478949068881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree113.table
  base := (38732666115900669336492420012890691748819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-671729367079611935529283300253778960000000000000)
      constant := (19601685098117666460570492568608502312141252170673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21163706518973368223/4000000000000000000)
  centralHi := (66136582871791775697/12500000000000000000)
  directionLo := (531449434830114433537/100000000000000000000)
  directionHi := (265724717415057216769/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree114.table
  base := (20043507660609827400669885949593697770809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-112675440120179236555218818439993510000000000000)
      constant := (3310394311164741242003669319362804418617446534001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree114.table
  base := (40087015281483626822793364301697868313063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-225891005169263037762190415663110770000000000000)
      constant := (6651997110210236120372525061293211846897189586607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531449434830114433537/100000000000000000000)
  centralHi := (265724717415057216769/50000000000000000000)
  directionLo := (66724475169960087383/12500000000000000000)
  directionHi := (106759160271936139813/20000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree115.table
  base := (10365254428447289445059546159882201339843/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-170495518833833513978388682904515946250000000000)
      constant := (5054552988075904881484452670223028317041079230081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree115.table
  base := (41461017679798615792866251229635831985669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-683616663935966291043859193724885660000000000000)
      constant := (20313487053328104593377572933539885073348396809623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66724475169960087383/12500000000000000000)
  centralHi := (106759160271936139813/20000000000000000000)
  directionLo := (134032974794730863017/25000000000000000000)
  directionHi := (536131899178923452069/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree116.table
  base := (8570934667500376285977751308422582009249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-687911509949592692495796552596166510000000000000)
      constant := (20577233121505068589113160027084215180595973127415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree116.table
  base := (42854673308428275950914190784653593954897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-689560312364143468801147140460439010000000000000)
      constant := (20674172266188475377459259144553038747446695025499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134032974794730863017/25000000000000000000)
  centralHi := (536131899178923452069/100000000000000000000)
  directionLo := (538457861940166110659/100000000000000000000)
  directionHi := (26922893097008305533/5000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree117.table
  base := (2766748886893431320038544334977222263311/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-57820078713654277423169864464522436250000000000)
      constant := (1744952447881212465443528674397348523851339050716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree117.table
  base := (44267982165428815396802173043492953814963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-231834653597440215519478362398664120000000000000)
      constant := (7012682323064876432935134151036717176219400455707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538457861940166110659/100000000000000000000)
  centralHi := (26922893097008305533/5000000000000000000)
  directionLo := (270386910210697253249/50000000000000000000)
  directionHi := (540773820421394506499/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree118.table
  base := (89259656778360788812399708153063374191/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-174942594794527491415070048638092990000000000000)
      constant := (5326200177874372911691357602030355824831062463616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree118.table
  base := (9140188849850960146922138905206006673409/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-701447609220497824315723033931545710000000000000)
      constant := (21405111162332898131831774059925578645117054981015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270386910210697253249/50000000000000000000)
  centralHi := (540773820421394506499/100000000000000000000)
  directionLo := (543079902612061571247/100000000000000000000)
  directionHi := (33942493913253848203/6250000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree119.table
  base := (5894194947110150754633389533230147277467/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 76507500000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (5066806608609383575266005302987500000000000)
      linear := (-610466966948415745884534615510791250000000000)
      constant := (18748570183618004882721117320041895488014645202) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree119.table
  base := (47153559558695512489912371715307573171903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306030000000000000000000000000000000000000000
      center := (5141304)
      previous := (2570652)
      next := (2570652)
      square := (20267226434437534301064021211950000000000000)
      linear := (-2447720614701297585027719656287540000000000000)
      constant := (75347283202742470416070721498491180161779747509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (543079902612061571247/100000000000000000000)
  centralHi := (33942493913253848203/6250000000000000000)
  directionLo := (34086014612226660293/6250000000000000000)
  directionHi := (545376233795626564689/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree120.table
  base := (48625828108371617187417315215918692460839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-237209749468875746274921278836192470000000000000)
      constant := (7348356212286809824709908245548921422138182386671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree120.table
  base := (24312914046410550061811777438254482703433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-118889151012808696638383154567108735000000000000)
      constant := (3691468003160905484600941013156011919658681089537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34086014612226660293/6250000000000000000)
  centralHi := (545376233795626564689/100000000000000000000)
  directionLo := (109532587325795892299/20000000000000000000)
  directionHi := (68457867078622432687/12500000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree121.table
  base := (50117749864233304487671022167228578528829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-717558683020885875407005657486680135000000000000)
      constant := (22419965225284829407641819895344077217914430873343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree121.table
  base := (50117749850937039977331239303537076277203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-719278554505029357587586874138205760000000000000)
      constant := (22525440682445332451242575347648960419494949345201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109532587325795892299/20000000000000000000)
  centralHi := (68457867078622432687/12500000000000000000)
  directionLo := (21997605248755718863/4000000000000000000)
  directionHi := (68742516402361621447/12500000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree122.table
  base := (10325864968782729366000763214773020708547/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-723488117635144511989247478464782860000000000000)
      constant := (22798036897530725916334462129209960480214594250245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree122.table
  base := (51629324832545627562304113913022631659511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-725222202933206535344874820873759110000000000000)
      constant := (22905262836027870749769788112721240651439368373437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21997605248755718863/4000000000000000000)
  centralHi := (68742516402361621447/12500000000000000000)
  directionLo := (883532696313019249/160000000000000000)
  directionHi := (276103967597818515313/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree123.table
  base := (53160553047032187278106191663128204869763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-243139184083134382857163099814295195000000000000)
      constant := (7726427884531584712493642726324915629491294732907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree123.table
  base := (53160553037313428949295248742738330859583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-243721950453794571034054255869770820000000000000)
      constant := (7762758159903366274830055138878891350585497186887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (883532696313019249/160000000000000000)
  centralHi := (276103967597818515313/50000000000000000000)
  directionLo := (554466463783883427817/100000000000000000000)
  directionHi := (277233231891941713909/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree124.table
  base := (27355717236676000688613038053677307219133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-367673493431830892576865560210494155000000000000)
      constant := (11781852746737409323972280646873568756887039760511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree124.table
  base := (54711434465043779916565625338813030407099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-737109499789560890859450714344865810000000000000)
      constant := (23674475613490277324517300175871297043999502251433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554466463783883427817/100000000000000000000)
  centralHi := (277233231891941713909/50000000000000000000)
  directionLo := (556715829871021504181/100000000000000000000)
  directionHi := (278357914935510752091/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree125.table
  base := (11256393824551100443032727834538283999447/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-741276421477920421735972941399091035000000000000)
      constant := (23951302417169879477678160617584264761439685601745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree125.table
  base := (5628196911565356045217165551750768709943/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-371526574108869034308369330540209580000000000000)
      constant := (12031933118683835557136260053795038235879907233905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556715829871021504181/100000000000000000000)
  centralHi := (278357914935510752091/50000000000000000000)
  directionLo := (558956144072999528343/100000000000000000000)
  directionHi := (69869518009124941043/12500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree126.table
  base := (28936078497612002335256207476598700034457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-124534309348696509719702460396198960000000000000)
      constant := (4057012404113295228413179991747931263735882302673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree126.table
  base := (57872156989153589983905840965055959869977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-249665598881971748791342202605324170000000000000)
      constant := (8152148783780791961221336439101337679677120623953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558956144072999528343/100000000000000000000)
  centralHi := (69869518009124941043/12500000000000000000)
  directionLo := (140296878699450102067/25000000000000000000)
  directionHi := (561187514797800408269/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree127.table
  base := (14870499522705118591570911995701515332187/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-188283822676609423725114145838824121250000000000)
      constant := (6184005379001262802782263020779376117496205521929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree127.table
  base := (14870499521408022137062251682308923775973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-188735111268523106032828638637881465000000000000)
      constant := (6213053988853792968562288490528985443982353396791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140296878699450102067/25000000000000000000)
  centralHi := (561187514797800408269/100000000000000000000)
  directionLo := (563410048306654803001/100000000000000000000)
  directionHi := (281705024153327401501/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree128.table
  base := (30555746204837487132372098550508428533833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-379532362660348165741349202166699605000000000000)
      constant := (12566571845573434655596588020150929367703637585411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree128.table
  base := (61111492405240733739696902219145346716481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-760884093502269601888602501287079210000000000000)
      constant := (25251175049587400563171592180165021638168131264427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563410048306654803001/100000000000000000000)
  centralHi := (281705024153327401501/50000000000000000000)
  directionLo := (70702981096636179193/12500000000000000000)
  directionHi := (113124769754617886709/20000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree129.table
  base := (6276063995197239597216878787198894808689/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-127499026655825828010823370885250322500000000000)
      constant := (4255573491684476816900567395046966604550765726605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree129.table
  base := (62760639948182915019458460594969617349533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-255609247310148926548630149340877520000000000000)
      constant := (8551107877953620260377080639701693301742367392437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70702981096636179193/12500000000000000000)
  centralHi := (113124769754617886709/20000000000000000000)
  directionLo := (113565803667980687001/20000000000000000000)
  directionHi := (283914509169951717503/50000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree130.table
  base := (12885888143588425137645656519915197174137/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-770923594549213604647182046289604660000000000000)
      constant := (25936913292887054734555741491392843968328565612895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree130.table
  base := (32214720357351923885431955229592854279763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-386385695179311978701589197379092955000000000000)
      constant := (13029330854118860639225391534933730904542316668721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113565803667980687001/20000000000000000000)
  centralHi := (283914509169951717503/50000000000000000000)
  directionLo := (35626603573385057679/6250000000000000000)
  directionHi := (114005131434832184573/20000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree131.table
  base := (661178947078493480454026212003718226283/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-194213257290868060307355966816926846250000000000)
      constant := (6585890179872449043586034216100326379494081739025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree131.table
  base := (1322357894101645220641760311218603216329/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-389357519393400567580233170746869630000000000000)
      constant := (13233594636360223604582243217855725966556810896075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35626603573385057679/6250000000000000000)
  centralHi := (114005131434832184573/20000000000000000000)
  directionLo := (572213863520283545773/100000000000000000000)
  directionHi := (286106931760141772887/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree132.table
  base := (33913000960993868145340472487583319371589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-130463743962955146301944281374301685000000000000)
      constant := (4458897204986280424229286566845349990422868443421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree132.table
  base := (67826001919623416525844578595225649930199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-261552895738326104305918096076430870000000000000)
      constant := (8959635442437246129817637617419050131077070439711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (572213863520283545773/100000000000000000000)
  centralHi := (286106931760141772887/50000000000000000000)
  directionLo := (143598433437830662081/25000000000000000000)
  directionHi := (22975749350052905933/4000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree133.table
  base := (69553762360673315595992268067725362513411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-788711898391989514393907509223912835000000000000)
      constant := (27166380824173508858649750207539460653115397964737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree133.table
  base := (13910752471730650727321372699701351103491/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-790602335643155490675042234964845960000000000000)
      constant := (27293812872014477514258159520119855639600095180485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143598433437830662081/25000000000000000000)
  centralHi := (22975749350052905933/4000000000000000000)
  directionLo := (57656536241848675359/10000000000000000000)
  directionHi := (576565362418486753591/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree134.table
  base := (557040437689369678042326145316536016001/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-198660333251562037744037332550503890000000000000)
      constant := (6895638375565055578567736031554796197425131720544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree134.table
  base := (35650588011256743186311492439221992614149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-398272992035666334216165090850199655000000000000)
      constant := (13855954453415843396753406483568202944951561733783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57656536241848675359/10000000000000000000)
  centralHi := (576565362418486753591/100000000000000000000)
  directionLo := (57872884229899638187/10000000000000000000)
  directionHi := (578728842298996381871/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree135.table
  base := (9133530364128985170225694793961763381661/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-66714230635042232296532595931676523750000000000)
      constant := (2333491772015073685578211541487060889123405191658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree135.table
  base := (14613648582311500990423721379613529410077/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-267496544166503282063206042811984220000000000000)
      constant := (9377731477255497234881349744472324239025122464265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57872884229899638187/10000000000000000000)
  centralHi := (578728842298996381871/100000000000000000000)
  directionLo := (580884264442334735051/100000000000000000000)
  directionHi := (145221066110583683763/25000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree136.table
  base := (74854963027406445973976204537263247089221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306030000000000000000000000000000000000000000
      center := (5141304)
      previous := (2570652)
      next := (2570652)
      square := (20267226434437534301064021211950000000000000)
      linear := (-2790658139220641606022951460755090000000000000)
      constant := (98354408684908782790477578803613407150671430263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree136.table
  base := (74854963026146957199329871267795661396577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306030000000000000000000000000000000000000000
      center := (5141304)
      previous := (2570652)
      next := (2570652)
      square := (20267226434437534301064021211950000000000000)
      linear := (-2797346992829366864868187111320090000000000000)
      constant := (98815465213917269057395784869544390625719445931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580884264442334735051/100000000000000000000)
  centralHi := (145221066110583683763/25000000000000000000)
  directionLo := (4664253745719675859/800000000000000000)
  directionHi := (72878964776869935297/12500000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree137.table
  base := (76661336367724766505230021173442050207609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-812429636849024060722874793136323735000000000000)
      constant := (28850122039536683760696207400334965280438499427603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree137.table
  base := (76661336366648904044154763490091909084017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-814376929355864201704194021907059360000000000000)
      constant := (28985333952001730337206096815326394130978771780539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4664253745719675859/800000000000000000)
  centralHi := (72878964776869935297/12500000000000000000)
  directionLo := (585171291343537771057/100000000000000000000)
  directionHi := (292585645671768885529/50000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree138.table
  base := (122636504584925653882125356872248789623/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-68196589288606891442093051176202205000000000000)
      constant := (2439916254414854506439181846350594031787140871520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree138.table
  base := (39243681466716729806479000833976040369691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-136720096297340229910246994773768785000000000000)
      constant := (4902697991218113971942372583963965970877441970499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (585171291343537771057/100000000000000000000)
  centralHi := (292585645671768885529/50000000000000000000)
  directionLo := (117460613991352728593/20000000000000000000)
  directionHi := (293651534978381821483/50000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree139.table
  base := (40166521363828368494993959411049687308923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-412144253038770666943679217546264592500000000000)
      constant := (14855521575133298992839214458269631509514126494441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree139.table
  base := (80333042726871840121378713643644981996511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-826264226212218557218769915378166060000000000000)
      constant := (29850231432746234376257639914954693176487336352437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117460613991352728593/20000000000000000000)
  centralHi := (293651534978381821483/50000000000000000000)
  directionLo := (589427138625814255953/100000000000000000000)
  directionHi := (294713569312907127977/50000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree140.table
  base := (82198375748005115177329825250461464037191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-830217940691799970469600256070631910000000000000)
      constant := (30146266331404964809084963469330330461155815133997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree140.table
  base := (82198375747334757409235979885768187154721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-832207874640395734976057862113719410000000000000)
      constant := (30287464408317660645507731228197848247302322834507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (589427138625814255953/100000000000000000000)
  centralHi := (294713569312907127977/50000000000000000000)
  directionLo := (591543580403498675691/100000000000000000000)
  directionHi := (147885895100874668923/25000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree141.table
  base := (84083361995763606837020666596063755364483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-278715791768686202350614025682911545000000000000)
      constant := (10194888198798864008316250838238179198613723322987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree141.table
  base := (42041680997595551405929580941331633922497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-139691920511428818788890968141545460000000000000)
      constant := (5121314479004370868811358141575945214068940258233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (591543580403498675691/100000000000000000000)
  centralHi := (147885895100874668923/25000000000000000000)
  directionLo := (593652476862150511903/100000000000000000000)
  directionHi := (18551639901942203497/3125000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree142.table
  base := (3439520058851831402232576673597940951593/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-842076809920317243634083898026837360000000000000)
      constant := (31026237945244695170723062361891275243153064183275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree142.table
  base := (17197600294161375082371474102551618103233/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-844095171496750090490633755584826110000000000000)
      constant := (31171498829875165071947242811969582878935131076055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593652476862150511903/100000000000000000000)
  centralHi := (18551639901942203497/3125000000000000000)
  directionLo := (595753908130313313299/100000000000000000000)
  directionHi := (5957539081303133133/1000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree143.table
  base := (43956147087480908208150521578213931240637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-424003122267287940108162859502470042500000000000)
      constant := (15735493188976229827914398116035697548199334878079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree143.table
  base := (17582458834908863157953388410263335499571/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-850038819924927268247921702320379460000000000000)
      constant := (31618300275867683975157511476959803539843921547285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (595753908130313313299/100000000000000000000)
  centralHi := (5957539081303133133/1000000000000000000)
  directionLo := (597847952928265400269/100000000000000000000)
  directionHi := (59784795292826540027/10000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree144.table
  base := (89856240107117716402206562562917003181233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-284645226382944838932855846661014270000000000000)
      constant := (10639636631507678058753387058201153704991558013737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree144.table
  base := (8985624010676121238554148742419972450157/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-142663744725517407667534941509322135000000000000)
      constant := (5344715202001157716498569674511460410803054499865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (597847952928265400269/100000000000000000000)
  centralHi := (59784795292826540027/10000000000000000000)
  directionLo := (74991836075303587033/12500000000000000000)
  directionHi := (119986937720485739253/20000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree145.table
  base := (91819839268114756961864730853840304441773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-859865113763093153380809360961145535000000000000)
      constant := (32370008494959525474917831130846159437219326365391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree145.table
  base := (91819839267810352660238936493932916068713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-861926116781281623762497595791486160000000000000)
      constant := (32521471638296072189948810956467910102300288118371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74991836075303587033/12500000000000000000)
  centralHi := (119986937720485739253/20000000000000000000)
  directionLo := (301007095579352055363/50000000000000000000)
  directionHi := (602014191158704110727/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree146.table
  base := (23450772914574750415156883786247326650707/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-216448637094337947490762795484812065000000000000)
      constant := (8206070544816248557593187755958027590560068446769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree146.table
  base := (11725386457254886943522840427116507044819/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-216967441302364700379946385631759877500000000000)
      constant := (8244460388684533445797420530298376896823520405346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301007095579352055363/50000000000000000000)
  centralHi := (602014191158704110727/100000000000000000000)
  directionLo := (75510816911846765261/12500000000000000000)
  directionHi := (604086535294774122089/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree147.table
  base := (47902998639005473823960628014369764449247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-145287330498601737757548833819558497500000000000)
      constant := (5546955157907075315054530962656200191067916138983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree147.table
  base := (23951499319447261333181225391322856272997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-72817784469802998273089457438549405000000000000)
      constant := (2786450080111346026517028396355550589902003452733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75510816911846765261/12500000000000000000)
  centralHi := (604086535294774122089/100000000000000000000)
  directionLo := (606151794431411402691/100000000000000000000)
  directionHi := (151537948607852850673/25000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree148.table
  base := (19565711225517051376025514161854334511727/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-877653417605869063127534823895453710000000000000)
      constant := (33742354799494858294478117295147446127645141095545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree148.table
  base := (48914278063697905081939164343774197551927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-439878531032906578517180717999073105000000000000)
      constant := (16950074929046548001539438314524145980859988752509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (606151794431411402691/100000000000000000000)
  centralHi := (151537948607852850673/25000000000000000000)
  directionLo := (121642008148566122563/20000000000000000000)
  directionHi := (38013127546426913301/6250000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree149.table
  base := (99870768207350561764647013571936898052549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-883582852220127699709776644873556435000000000000)
      constant := (34206153735425119955581448680856291757903523386583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree149.table
  base := (624192301294930194053658712316112222761/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-221425177623497583697912345683424890000000000000)
      constant := (8591522061252969625509859270781299384127470447480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121642008148566122563/20000000000000000000)
  centralHi := (38013127546426913301/6250000000000000000)
  directionLo := (610261345186118863083/100000000000000000000)
  directionHi := (152565336296529715771/25000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree150.table
  base := (50966316758814666349078497577487158636447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-148252047805731056048669744308609860000000000000)
      constant := (5778854625872681481320831811230969758767364399783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree150.table
  base := (25483158379372817339090971721300864301729/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-74303696576847292712411444122437742500000000000)
      constant := (2902934676841279828376843592485589518738419945881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (610261345186118863083/100000000000000000000)
  centralHi := (152565336296529715771/25000000000000000000)
  directionLo := (612305777529778798437/100000000000000000000)
  directionHi := (306152888764889399219/50000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree151.table
  base := (26003538014684449231653958317216312140111/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-223860430362161243218565071707440471250000000000)
      constant := (8785819214732640472426168471859587997416233093637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree151.table
  base := (104014152058619942755641395407081616291007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-897588007350344690306225276204806260000000000000)
      constant := (35307533489346336338576825767376619527769215606869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (612305777529778798437/100000000000000000000)
  centralHi := (306152888764889399219/50000000000000000000)
  directionLo := (122868681276283357587/20000000000000000000)
  directionHi := (19198231449419274623/3125000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree152.table
  base := (106115323830985899809757141551945393129791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-901371156062903609456502107807864610000000000000)
      constant := (35616601046511280200437392868906174446259837258197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree152.table
  base := (5305766191544265054053459842444725909171/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-225882913944630467015878305735089902500000000000)
      constant := (8945760086691889849357826701054559073412630363285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122868681276283357587/20000000000000000000)
  centralHi := (19198231449419274623/3125000000000000000)
  directionLo := (616374299214607308567/100000000000000000000)
  directionHi := (77046787401825913571/12500000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree153.table
  base := (108236148834677300974260631889566045366137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6755742144812511433688007070650000000000000)
      linear := (-1046482803549206742835921486489005000000000000)
      constant := (41629873492480887505119519616131956353779963537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree153.table
  base := (108236148834591434973410402759974044859361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6755742144812511433688007070650000000000000)
      linear := (-1048991123652478714902884855450880000000000000)
      constant := (41824379116910861102542879195668972731610341561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (616374299214607308567/100000000000000000000)
  centralHi := (77046787401825913571/12500000000000000000)
  directionLo := (309199261197481641981/50000000000000000000)
  directionHi := (618398522394963283963/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree154.table
  base := (344926959594091871956684885154207862771/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-228307506322855220655246437441017515000000000000)
      constant := (9143193668335534990471342833105504166572686708560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree154.table
  base := (11037662707003611126844772375906084639159/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-457709476317438111789044558205733155000000000000)
      constant := (18371811266065720701698170794676393117366604257265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309199261197481641981/50000000000000000000)
  centralHi := (618398522394963283963/100000000000000000000)
  directionLo := (620416141205440876539/100000000000000000000)
  directionHi := (31020807060272043827/5000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree155.table
  base := (22507351707514675899386378475079001064979/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-919159459905679519203227570742172785000000000000)
      constant := (37055624112597487007865105567812749566934793126965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree155.table
  base := (112536758537510830071302297595555700101207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-921362601063053401335377063147019660000000000000)
      constant := (37228697860079311984666522193941076487567001730269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620416141205440876539/100000000000000000000)
  centralHi := (31020807060272043827/5000000000000000000)
  directionLo := (622427219870906030687/100000000000000000000)
  directionHi := (19450850620965813459/3125000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree156.table
  base := (114716543237354281547838315064902947705331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-308362964839979385261823130573425170000000000000)
      constant := (12513882878583163855774976864818114586197661562459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree156.table
  base := (114716543237300899264335830871669623879993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-309102083163743526364221669960857670000000000000)
      constant := (12572320892735950552934676533391829049794744683377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (622427219870906030687/100000000000000000000)
  centralHi := (19450850620965813459/3125000000000000000)
  directionLo := (156107955395497230403/25000000000000000000)
  directionHi := (624431821581988921613/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree157.table
  base := (116915981169731079674538250035402559996669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-931018329134196792367711212698378235000000000000)
      constant := (38030848242800620965190829075596251747469059746623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree157.table
  base := (116915981169685522883085954319538105511303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-933249897919407756849952956618126360000000000000)
      constant := (38208416986519529780846636102798429954316135249901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156107955395497230403/25000000000000000000)
  centralHi := (624431821581988921613/100000000000000000000)
  directionLo := (156607502129562844107/25000000000000000000)
  directionHi := (626430008518251376429/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree158.table
  base := (11913507233497677726310329730126621634241/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-468473881874227714474976516838240480000000000000)
      constant := (19261611466876644858150561161441393323956018731735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree158.table
  base := (23827014466987580074933082130174370880657/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-939193546347584934607240903353679710000000000000)
      constant := (38703060785016762599648859177454578443127778217095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156607502129562844107/25000000000000000000)
  centralHi := (626430008518251376429/100000000000000000000)
  directionLo := (314210920935345648943/50000000000000000000)
  directionHi := (628421841870691297887/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree159.table
  base := (242747633466717018722120305866284777443/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-78573099863559505461016237887881973750000000000)
      constant := (3251564392384155036195099510499217867437144553375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree159.table
  base := (60686908366662667121508098428718745847593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-157522865795960352060754808348205510000000000000)
      constant := (6533482345616985701654221733008718902477084599777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314210920935345648943/50000000000000000000)
  centralHi := (628421841870691297887/100000000000000000000)
  directionLo := (12608147637272142681/2000000000000000000)
  directionHi := (630407381863607134051/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree160.table
  base := (61816107182568826230840442135027474326949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-474403316488486351057218337816343205000000000000)
      constant := (19758748783686322401402533176054020835283182251383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree160.table
  base := (123632214365109343999143532004375059187757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-951080843203939290121816796824786410000000000000)
      constant := (39701916852577297560057089360397223791597326039119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12608147637272142681/2000000000000000000)
  centralHi := (630407381863607134051/100000000000000000000)
  directionLo := (632386687775844496683/100000000000000000000)
  directionHi := (158096671943961124171/25000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree161.table
  base := (12591026523056993946612872764283395591919/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-477368033795615669348339248305394567500000000000)
      constant := (20009698755021952295875655636964514906095273391865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree161.table
  base := (31477566307636446170912540005437597241749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-239256122908029116969776185890084940000000000000)
      constant := (10051532280411293875084130643184860279969491702983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (632386687775844496683/100000000000000000000)
  centralHi := (158096671943961124171/25000000000000000000)
  directionLo := (126871963592289226903/20000000000000000000)
  directionHi := (158589954490361533629/25000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree162.table
  base := (128207969329905578297504773347976875522919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1952409479850815804335834043417850000000000000)
      linear := (-320221834068496658426306772529630620000000000000)
      constant := (13508157512208617568952450134008970526483486751791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree162.table
  base := (64103984664942484261726787943629209908683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-160494690010048940939398781715982185000000000000)
      constant := (6785588480151293643155308824605476413810479356787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126871963592289226903/20000000000000000000)
  centralHi := (158589954490361533629/25000000000000000000)
  directionLo := (318163414934862806369/50000000000000000000)
  directionHi := (636326829869725612739/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree163.table
  base := (130525326663389372901873112054966886304699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-966594936819748611861162138566994585000000000000)
      constant := (41032722647120654259584828153394804958012401310633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree163.table
  base := (522101306653487154131557787237163171231/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-484455894244235411696840318515723230000000000000)
      constant := (20612061065183611267524149976745818097366710334625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318163414934862806369/50000000000000000000)
  centralHi := (636326829869725612739/100000000000000000000)
  directionLo := (638287780064784234711/100000000000000000000)
  directionHi := (79785972508098029339/12500000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree164.table
  base := (13286233723126084559140853993181771399063/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44221335000000000000000000000000000000000000000
      center := (742918428)
      previous := (371459214)
      next := (371459214)
      square := (2928614219776223706503751065126775000000000000)
      linear := (-486262185717003624221701979772548655000000000000)
      constant := (20772073920765213824607537888006600098931383609105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree164.table
  base := (33215584307811460769648593152286350246311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-243713859229162000287742145941749952500000000000)
      constant := (10434475717506419150153290392776871277033890249037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (638287780064784234711/100000000000000000000)
  centralHi := (79785972508098029339/12500000000000000000)
  directionLo := (640242724244489964009/100000000000000000000)
  directionHi := (64024272424448996401/10000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree165.table
  base := (13521900103375435987019986889817483769581/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-163075634341377647504274296753866672500000000000)
      constant := (7009791353309540941525551719035370743606401403545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree165.table
  base := (67609500516870780301822097183393163325097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-163466514224137529818042755083758860000000000000)
      constant := (7042478849980866233894899140040195986223921889633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (640242724244489964009/100000000000000000000)
  centralHi := (64024272424448996401/10000000000000000000)
  directionLo := (321095858629468181281/50000000000000000000)
  directionHi := (642191717258936362563/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree166.table
  base := (8599707379443702689955179551410205037191/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-246095810165631130401971900375325690000000000000)
      constant := (10644130870525784122820070382159183987619648535988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree166.table
  base := (34398829517772080963625928194783078875017/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-246685683443250589166386119309526627500000000000)
      constant := (10693758204986953416392981941089511021652709977539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321095858629468181281/50000000000000000000)
  centralHi := (642191717258936362563/100000000000000000000)
  directionLo := (644134813128398851989/100000000000000000000)
  directionHi := (64413481312839885199/10000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree167.table
  base := (139991288343519908008686501928450587339323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-990312675276783158190129422479405485000000000000)
      constant := (43097473928270084943290532432792791295110792211241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree167.table
  base := (27998257668702118615748552534202260079617/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-992686382201179534422832423973659860000000000000)
      constant := (43298382030215510573581154063794766083237870028695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (644134813128398851989/100000000000000000000)
  centralHi := (64413481312839885199/10000000000000000000)
  directionLo := (646072065060804928541/100000000000000000000)
  directionHi := (323036032530402464271/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree168.table
  base := (71203455925617986927240879997748087081701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (976204739925407902167917021708925000000000000)
      linear := (-166040351648506965795395207242918035000000000000)
      constant := (7270266576393338895821854715844284590296604819389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree168.table
  base := (17800863981403503470731718206553357377471/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (488102369962703951083958510854462500000000000)
      linear := (-83219169219113059348343364225767767500000000000)
      constant := (3652076727557519237880935686071786951595182205838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell076.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (646072065060804928541/100000000000000000000)
  centralHi := (323036032530402464271/50000000000000000000)
  directionLo := (648003525468734315697/100000000000000000000)
  directionHi := (324001762734367157849/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree169.table
  base := (9052636787153899046954226067679793771297/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22110667500000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (1464307109888111853251875532563387500000000000)
      linear := (-250542886126325107838653266108902733750000000000)
      constant := (11037225018093720702468079256145962216316900417196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree169.table
  base := (144842188594455606590967944518589931518487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88442670000000000000000000000000000000000000000
      center := (1485836856)
      previous := (742918428)
      next := (742918428)
      square := (5857228439552447413007502130253550000000000000)
      linear := (-1004573679057533889937408317444766560000000000000)
      constant := (44354648921373875837344317596651427970361214464029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell076.Kernel169
