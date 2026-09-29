import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell019.Parameters
import ForestUnimodality.BinomialMassData.Q101_255.Batch000_049
import ForestUnimodality.BinomialMassData.Q101_255.Batch050_099
import ForestUnimodality.BinomialMassData.Q101_255.Batch100_149
import ForestUnimodality.BinomialMassData.Q101_255.Batch150_199
import ForestUnimodality.BinomialMassData.Q103_255.Batch000_049
import ForestUnimodality.BinomialMassData.Q103_255.Batch050_099
import ForestUnimodality.BinomialMassData.Q103_255.Batch100_149
import ForestUnimodality.BinomialMassData.Q103_255.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree000.table
  base := (3372890584608298401246173571/200000000000000000000000000)
  polynomial :=
    { denominator := 425000000000000000000000000000000000000000
      center := (1078)
      previous := (707)
      next := (0)
      square := (9787132691653019876676378375000000000000)
      linear := (32824625015719651605072826275000000000000)
      constant := (7167392492292634102648118838375000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree000.table
  base := (3372890584608298401246173571/200000000000000000000000000)
  polynomial :=
    { denominator := 425000000000000000000000000000000000000000
      center := (1064)
      previous := (721)
      next := (0)
      square := (9787132691653019876676378375000000000000)
      linear := (32824625015719651605072826275000000000000)
      constant := (7167392492292634102648118838375000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree001.table
  base := (107867489743226994938829638657684544405997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (2557311430117840457681976907350000000000000)
      constant := (466436062661685403967549346475322499999996995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree001.table
  base := (1666698218695784088174887458327791594579/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (1270826008905597812939647350975000000000000)
      constant := (230609626242332400271200326976931249999998880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12227027121657833617/25000000000000000000)
  directionHi := (48908108486631334469/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree002.table
  base := (70337037189550427374493052036891441753171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (1766511108632276451646525534650000000000000)
      constant := (302885264417156774149008716519984399999996285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree002.table
  base := (68869662592366281358866950549975865282583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (1735192284018986788041161123850000000000000)
      constant := (296496731198028981459585741580805375999997305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12227027121657833617/25000000000000000000)
  centralHi := (48908108486631334469/100000000000000000000)
  directionLo := (34583255165904351011/50000000000000000000)
  directionHi := (69166510331808702023/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree003.table
  base := (5870417652083829710126000068421009407189/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (162618464524452074268512360325000000000000)
      constant := (33502870816874181010957516918373434373552420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree003.table
  base := (45604855008251829674559149614536860414001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (309577516742259316734342515250000000000000)
      constant := (65035260657338582529475604624265763298231445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34583255165904351011/50000000000000000000)
  centralHi := (69166510331808702023/100000000000000000000)
  directionLo := (16942265760187212793/20000000000000000000)
  directionHi := (42355664400468031983/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree004.table
  base := (16108875480249113732088421887730594776731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (92455232830574219787811394625000000000000)
      constant := (68432621309061398839455865126452128357128885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree004.table
  base := (31086508891282578166348804412026511046103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (122272816434569112364893967650000000000000)
      constant := (131956489686785182011228112682894925384856505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16942265760187212793/20000000000000000000)
  centralHi := (42355664400468031983/50000000000000000000)
  directionLo := (97816216973262668937/100000000000000000000)
  directionHi := (48908108486631334469/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree005.table
  base := (11368749686028086130188028109055115891787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-302944927912207783229914291725000000000000)
      constant := (47925861205237253969350309846103927390896645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree005.table
  base := (2183991754875445050144261713417222969209/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-342093458678819862736619805225000000000000)
      constant := (45993000414732556912665346006118307857605075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97816216973262668937/100000000000000000000)
  centralHi := (48908108486631334469/50000000000000000000)
  directionLo := (54680927613521014151/50000000000000000000)
  directionHi := (109361855227042028303/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree006.table
  base := (8247227372273209017430902743804053346829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-232781696218329928749213326025000000000000)
      constant := (11530785554888442100749542737906857086167905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree006.table
  base := (15795867394489883671229664317130025588661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-496882217049949521103791062850000000000000)
      constant := (22074758167991935796135399548352886975615145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54680927613521014151/50000000000000000000)
  centralHi := (109361855227042028303/100000000000000000000)
  directionLo := (119799910076930357307/100000000000000000000)
  directionHi := (29949977519232589327/25000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree007.table
  base := (12256060839842305302144119548040494424039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-2187490498795543578530731328850000000000000)
      constant := (51521084082412162806702611682915543328209065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree007.table
  base := (2928190945669841302380380387369999543207/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-1148553192471028700574753383325000000000000)
      constant := (24644498960366513079763906378927896039604690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119799910076930357307/100000000000000000000)
  centralHi := (29949977519232589327/25000000000000000000)
  directionLo := (129398692150194082751/100000000000000000000)
  directionHi := (2021854564846782543/1562500000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree008.table
  base := (144874172694942999636291951619114839839/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-1489145410140553792283091350775000000000000)
      constant := (19803989047508751852336413227203610582466080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree008.table
  base := (8844140209215508321358685994964614430619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-3103566118734266238987640344750000000000000)
      constant := (37944238784431248382546089555451603556733365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129398692150194082751/100000000000000000000)
  centralHi := (2021854564846782543/1562500000000000000)
  directionLo := (34583255165904351011/25000000000000000000)
  directionHi := (27666604132723480809/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree009.table
  base := (3541977382441705958831217505477978365363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-628181856961111931766939012375000000000000)
      constant := (5243212960000294462909064546045678737949535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree009.table
  base := (6739739828116423347702981926615845358709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-1303341950842158358941924640950000000000000)
      constant := (10079377889246327461843512420479896543334505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34583255165904351011/25000000000000000000)
  centralHi := (27666604132723480809/20000000000000000000)
  directionLo := (29344865091978800681/20000000000000000000)
  directionHi := (73362162729947001703/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree010.table
  base := (2705563749063150902132012579882441749369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-2279945731626117798318542723475000000000000)
      constant := (12928518370586131164907817414740384983514615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree010.table
  base := (1281662411514579426922734492110136995409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-2358242793159341957331953750475000000000000)
      constant := (12493802372298793665219003730444887750196030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29344865091978800681/20000000000000000000)
  centralHi := (73362162729947001703/50000000000000000000)
  directionLo := (77330509434182896141/50000000000000000000)
  directionHi := (154661018868365792283/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree011.table
  base := (4080094546019973812816717284707342978069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-5350691784737799602672536819650000000000000)
      constant := (22049693027216808045970519600766331809929115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree011.table
  base := (3838277693735589446248781366775646123441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-5522945320110892752502041079050000000000000)
      constant := (21470475828067278742023695266672425945116735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77330509434182896141/50000000000000000000)
  centralHi := (154661018868365792283/100000000000000000000)
  directionLo := (32441969011230560373/20000000000000000000)
  directionHi := (81104922528076400933/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree012.table
  base := (596584586240736601773358782098646559639/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-2047164035407787869569329397450000000000000)
      constant := (6523119053758858211687392111582721393391775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree012.table
  base := (554381075709728462389743828629585261061/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-2109801684634367196780058219050000000000000)
      constant := (6413820606409602290116039372368753511165725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32441969011230560373/20000000000000000000)
  centralHi := (81104922528076400933/50000000000000000000)
  directionLo := (16942265760187212793/10000000000000000000)
  directionHi := (169422657601872127931/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree013.table
  base := (2051588018071767155505351367095972768281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-6932292427708927614743439565050000000000000)
      constant := (18121142348001016300090507621861041950498135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree013.table
  base := (1863304627379010918537711850644080246879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-7135864787695310428178308235250000000000000)
      constant := (18022134021113624266004350009822087870220465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16942265760187212793/10000000000000000000)
  centralHi := (169422657601872127931/100000000000000000000)
  directionLo := (44085173233626191783/25000000000000000000)
  directionHi := (176340692934504767133/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree014.table
  base := (1242498827134711242135483519000751502741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-7723092749194491620778890937750000000000000)
      constant := (17516081691303085470117925364648257764382235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree014.table
  base := (1071546490744195900595992555833749618833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-7942324521487519266016441813350000000000000)
      constant := (17635065437715096179897701288399304597641055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44085173233626191783/25000000000000000000)
  centralHi := (176340692934504767133/100000000000000000000)
  directionLo := (182997385392145424121/100000000000000000000)
  directionHi := (91498692696072712061/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree015.table
  base := (65888448977949973032272206484349911567/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-1418982178446675937802390385075000000000000)
      constant := (2938403437184422253306868241079542488857260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree015.table
  base := (369897449039491518674061678819664937579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-2916261418426576034618191797150000000000000)
      constant := (5988122087182274410504863757994415834801655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (182997385392145424121/100000000000000000000)
  centralHi := (91498692696072712061/50000000000000000000)
  directionLo := (4735507241580719739/2500000000000000000)
  directionHi := (189420289663228789561/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree016.table
  base := (-91038402571869941249720051464288373/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-4652346696082809816424896841575000000000000)
      constant := (9190436878177467047846051982043943689403125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree016.table
  base := (-129823339114754782646644677221218312981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-4777621994535968470846354484775000000000000)
      constant := (9465994185082774805171170399046018613227365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4735507241580719739/2500000000000000000)
  centralHi := (189420289663228789561/100000000000000000000)
  directionLo := (97816216973262668937/50000000000000000000)
  directionHi := (1565059471572202703/800000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree017.table
  base := (-13871450663578211931546481813924937191/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1275000000000000000000000000000000000000000
      center := (3234)
      previous := (2121)
      next := (0)
      square := (29361398074959059630029135125000000000000)
      linear := (-296926285695623048202507207525000000000000)
      constant := (579692617869518013340263231726228525407375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree017.table
  base := (-829652083793302094608357053797817301073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2550000000000000000000000000000000000000000
      center := (6384)
      previous := (4326)
      next := (0)
      square := (58722796149918119260058270250000000000000)
      linear := (-609511983697890928207696620450000000000000)
      constant := (1204909254004975329656793793561556588226385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97816216973262668937/50000000000000000000)
  centralHi := (1565059471572202703/800000000000000000)
  directionLo := (201653297239548501627/100000000000000000000)
  directionHi := (50413324309887125407/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree018.table
  base := (-12218392195944058246004054245154367757/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-1814382339189457940820116071425000000000000)
      constant := (3595788285236380975852854627837596929556750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree018.table
  base := (-674618552337089341978819609189653371301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-1861360576109392436228162687625000000000000)
      constant := (3763207519052046288053014065350950878470055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201653297239548501627/100000000000000000000)
  centralHi := (50413324309887125407/25000000000000000000)
  directionLo := (103749765497713053033/50000000000000000000)
  directionHi := (207499530995426106067/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree019.table
  base := (-426449159223324518556447465544529025143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-5838547178311155825478073900625000000000000)
      constant := (11972605023878171416577465925868933352010190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree019.table
  base := (-1825282844990032013236377435407150429459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-11974623190448563455207109703850000000000000)
      constant := (25189522172497576215454238222170002888295235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103749765497713053033/50000000000000000000)
  centralHi := (207499530995426106067/100000000000000000000)
  directionLo := (106592751206474987097/50000000000000000000)
  directionHi := (42637100482589994839/20000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree020.table
  base := (-2151027478182887297737849214199166910003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-12467894678107875656991599173950000000000000)
      constant := (26796789041957638094529610334246611445136995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree020.table
  base := (-1131587990864393693810983721908377405893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-6390541462120386146522621640975000000000000)
      constant := (14145468623948909933814972726227183945453845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106592751206474987097/50000000000000000000)
  centralHi := (42637100482589994839/20000000000000000000)
  directionLo := (54680927613521014151/25000000000000000000)
  directionHi := (43744742090816811321/20000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree021.table
  base := (-2562004168963844819755995764470089987787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-4419564999864479887675683515550000000000000)
      constant := (10036692909825587149005336987960719967647785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree021.table
  base := (-533454013051479291187334177488015395013/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-4529180886010993710294458953350000000000000)
      constant := (10621539233224091095733567285649088771031075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54680927613521014151/25000000000000000000)
  centralHi := (43744742090816811321/20000000000000000000)
  directionLo := (56031277309275051003/25000000000000000000)
  directionHi := (224125109237100204013/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree022.table
  base := (-2942409331704040820337680168392760735893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-14049495321079003669062501919350000000000000)
      constant := (33869114941915495660065085149477382209903845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree022.table
  base := (-304117676575302389484497817794416712833/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-7197001195912594984360755219075000000000000)
      constant := (17947453468801463800412970750536017749344725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56031277309275051003/25000000000000000000)
  centralHi := (224125109237100204013/100000000000000000000)
  directionLo := (114699681414424817/50000000000000000)
  directionHi := (229399362828849634001/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree023.table
  base := (-164767132664871672075725069855702785329/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-7420147821282283837548976646025000000000000)
      constant := (19030230268294266093984925675555284255987850) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree023.table
  base := (-169397690568204120133314330746802825781/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-7600231062808699403279822008125000000000000)
      constant := (20184274855083206880645538545516097502393650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114699681414424817/50000000000000000)
  centralHi := (229399362828849634001/100000000000000000000)
  directionLo := (23455504842578489919/10000000000000000000)
  directionHi := (234555048425784899191/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree024.table
  base := (-3623457600617101565922471728068284778483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-5210365321350043893711134888250000000000000)
      constant := (14224204244867024691501065448701328495092065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree024.table
  base := (-3710229658524840624978850210268409585007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-5335640619803202548132592531450000000000000)
      constant := (15091383886240059063338125828482148149664885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23455504842578489919/10000000000000000000)
  centralHi := (234555048425784899191/100000000000000000000)
  directionLo := (119799910076930357307/50000000000000000000)
  directionHi := (47919964030772142923/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree025.table
  base := (-785810883188337695978976744845874236519/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-16421896285535695687168856037450000000000000)
      constant := (47695599985675202673410296873965675923450675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree025.table
  base := (-1002572243625104149751950462948209083249/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-8406690796600908241117955586225000000000000)
      constant := (25300904375334965597812445807739027248231170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119799910076930357307/50000000000000000000)
  centralHi := (47919964030772142923/20000000000000000000)
  directionLo := (122270271216578336171/50000000000000000000)
  directionHi := (244540542433156672343/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree026.table
  base := (-4214145519759926048219533809627839473613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-17212696607021259693204307410150000000000000)
      constant := (53120698446992265350836055436523315881887645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree026.table
  base := (-4290133466794287249420577021900194025411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-17619841326994025320074044750550000000000000)
      constant := (56342843583988103309689286664962658899843315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122270271216578336171/50000000000000000000)
  centralHi := (244540542433156672343/100000000000000000000)
  directionLo := (62345849886561514717/25000000000000000000)
  directionHi := (249383399546246058869/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree027.table
  base := (-14001572507377894585382404691508661593/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-3000582821417803949873293130475000000000000)
      constant := (9823370873358160267045664924583197439698400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree027.table
  base := (-4551526879058389504324643503315299614831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-6142100353595411385970726109550000000000000)
      constant := (20829870109981182316287229931929392056569205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62345849886561514717/25000000000000000000)
  centralHi := (249383399546246058869/100000000000000000000)
  directionLo := (50826797280561638379/20000000000000000000)
  directionHi := (31766748300351023987/12500000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree028.table
  base := (-4729695694739037792621916377935000838681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-18794297249992387705275210155550000000000000)
      constant := (65147382083784790006484790823051771364317865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree028.table
  base := (-1199007386509740590255893280731558660919/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-9616380397289221497875155953375000000000000)
      constant := (34517672468705658029915558569197386409832270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50826797280561638379/20000000000000000000)
  centralHi := (31766748300351023987/12500000000000000000)
  directionLo := (129398692150194082751/50000000000000000000)
  directionHi := (258797384300388165503/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree029.table
  base := (-496311540438978487815673262824086967847/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-9792548785738975855655330764125000000000000)
      constant := (35868066445703326461105654757677914971916275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree029.table
  base := (-2512512920058147444615926860123173072031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-10019610264185325916794222742425000000000000)
      constant := (37987023076061428762692631954246044732745615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129398692150194082751/50000000000000000000)
  centralHi := (258797384300388165503/100000000000000000000)
  directionLo := (52675644921144686023/20000000000000000000)
  directionHi := (65844556151430857529/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree030.table
  base := (-5182001696386091007610959631352652993851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-6791965964321171905782037633650000000000000)
      constant := (26233701671807809015894264248595416423885305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree030.table
  base := (-5239746599504878806029374937295275545881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-6948560087387620223808859687650000000000000)
      constant := (27766792763472783250660936169308326836201955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52675644921144686023/20000000000000000000)
  centralHi := (65844556151430857529/25000000000000000000)
  directionLo := (267880742630378339121/100000000000000000000)
  directionHi := (133940371315189169561/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree031.table
  base := (-2693729870093405194438111452200978998801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-10583349107224539861690782136825000000000000)
      constant := (43018753773115489695844521948788756040197665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree031.table
  base := (-5441287875001709375958100354022715693509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-21652139995955069509264712641050000000000000)
      constant := (91009589972092818267834338817611527468638485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267880742630378339121/100000000000000000000)
  centralHi := (133940371315189169561/50000000000000000000)
  directionLo := (272308823485290499699/100000000000000000000)
  directionHi := (2723088234852904997/1000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree032.table
  base := (-1395119103371587070679398276914066670139/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-10978749267967321864708507823175000000000000)
      constant := (46870531184512031574406740829235041969894870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree032.table
  base := (-5630626872316534266579618667421602971559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-22458599729747278347102846219150000000000000)
      constant := (99097445010394506934060367836087351118291735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272308823485290499699/100000000000000000000)
  centralHi := (2723088234852904997/1000000000000000000)
  directionLo := (34583255165904351011/12500000000000000000)
  directionHi := (276666041327234808089/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree033.table
  base := (-1440483481573417385405569979904692882389/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-3791383142903367955908744503175000000000000)
      constant := (16967990850568969280587342012025437569895790) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree033.table
  base := (-5808635683393128812176634267439260880857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-7755019821179829061646993265750000000000000)
      constant := (35853387628915716558848457344310268027161635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34583255165904351011/12500000000000000000)
  centralHi := (276666041327234808089/100000000000000000000)
  directionLo := (140477846562565959213/50000000000000000000)
  directionHi := (280955693125131918427/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree034.table
  base := (-59326216227672949684079659957558994207/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1275000000000000000000000000000000000000000
      center := (3234)
      previous := (2121)
      next := (0)
      square := (29361398074959059630029135125000000000000)
      linear := (-692326446438405051220232893875000000000000)
      constant := (3242198057131560273988414730211122823860750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree034.table
  base := (-1494023305682627920559197793023535274037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1275000000000000000000000000000000000000000
      center := (3192)
      previous := (2163)
      next := (0)
      square := (29361398074959059630029135125000000000000)
      linear := (-707985858745049883022915099275000000000000)
      constant := (3423363735494044134207659252647997010241130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140477846562565959213/50000000000000000000)
  centralHi := (280955693125131918427/100000000000000000000)
  directionLo := (71295206963355625133/25000000000000000000)
  directionHi := (285180827853422500533/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree035.table
  base := (-1218649257506668256013963630913304801009/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-24329899500391335747523369764450000000000000)
      constant := (119018364974847548076885579765354118438129925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree035.table
  base := (-95838994869462955369928883293398238349/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-12438989465561952430308623476725000000000000)
      constant := (62798519712268298763263706797389796376226720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71295206963355625133/25000000000000000000)
  centralHi := (285180827853422500533/100000000000000000000)
  directionLo := (904200849523132487/312500000000000000)
  directionHi := (289344271847402395841/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree036.table
  base := (-6244441198410450346441670080228323646187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-8373566607292299917852940379050000000000000)
      constant := (42718697647064499820544273288590072331259785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree036.table
  base := (-1570516414894999578691623262300802177287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-4280739777486018949742563421925000000000000)
      constant := (22527580173555910643204845029650681707640570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (904200849523132487/312500000000000000)
  centralHi := (289344271847402395841/100000000000000000000)
  directionLo := (293448650919788006811/100000000000000000000)
  directionHi := (73362162729947001703/25000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree037.table
  base := (-6386774111125431657190783867210023465607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-25911500143362463759594272509850000000000000)
      constant := (137645456620435184332140239948904548276593655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree037.table
  base := (-642176036186600408586831447310844345741/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-13245449199354161268146757054825000000000000)
      constant := (72548638251064105530730882395817448806063825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293448650919788006811/100000000000000000000)
  centralHi := (73362162729947001703/25000000000000000000)
  directionLo := (297496409730241448131/100000000000000000000)
  directionHi := (74374102432560362033/25000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree038.table
  base := (-6520754323053037289350067794969799659173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-26702300464848027765629723882550000000000000)
      constant := (147484248208453052434470182623305918477485045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree038.table
  base := (-3276639329376067689289267112388174929819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-13648679066250265687065823843875000000000000)
      constant := (77695131580518819829049904285187261679234635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297496409730241448131/100000000000000000000)
  centralHi := (74374102432560362033/25000000000000000000)
  directionLo := (301489828813716033359/100000000000000000000)
  directionHi := (3768622860171450417/1250000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree039.table
  base := (-3323419467866837536016537125939895174371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-4582183464388931961944195875875000000000000)
      constant := (26278414361678239304902566380896851473033905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree039.table
  base := (-3338533737722385070420100200850958847459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-4683969644382123368661630210975000000000000)
      constant := (27673750599549016874135014668580364465421745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301489828813716033359/100000000000000000000)
  centralHi := (3768622860171450417/1250000000000000000)
  directionLo := (9544719987639512381/3125000000000000000)
  directionHi := (305431039604464396193/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree040.table
  base := (-169135960397852907150562976299848717109/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-14141950553909577888850313313975000000000000)
      constant := (84101195565968540507391406940603116226649700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree040.table
  base := (-1698381851027489376804611968552836742013/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-14455138800042474524903957421975000000000000)
      constant := (88526130621928886411626371726046905446747290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9544719987639512381/3125000000000000000)
  centralHi := (305431039604464396193/100000000000000000000)
  directionLo := (77330509434182896141/25000000000000000000)
  directionHi := (61864407547346316913/20000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree041.table
  base := (-3438460769823872085132653703809745181443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-14537350714652359891868039000325000000000000)
      constant := (89539182224932285824868797657714754638444595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree041.table
  base := (-1725754423533615770541804602472089314519/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-14858368666938578943823024211025000000000000)
      constant := (94208989377318512749059968664866985643120270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77330509434182896141/25000000000000000000)
  centralHi := (61864407547346316913/20000000000000000000)
  directionLo := (19572793428609018671/6250000000000000000)
  directionHi := (313164694857744298737/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree042.table
  base := (-1396323958408481095992199814055135120609/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-9955167250263427929923843124450000000000000)
      constant := (63432323045303130683496550355071648753599975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree042.table
  base := (-875732585648758802974978490092568989101/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-5087199511278227787580697000025000000000000)
      constant := (33356376464525779590831740860974951242996220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19572793428609018671/6250000000000000000)
  centralHi := (313164694857744298737/100000000000000000000)
  directionLo := (63392153830291710127/20000000000000000000)
  directionHi := (79240192287864637659/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree043.table
  base := (-1769957821395752658574191415036444704011/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-15328151036137923897903490373025000000000000)
      constant := (100928456436224727774931296078534024416224630) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree043.table
  base := (-7102345747967196239673435545658079933393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-31329656801461575563322315578250000000000000)
      constant := (212211846919467772536603982093352223488741345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63392153830291710127/20000000000000000000)
  centralHi := (79240192287864637659/25000000000000000000)
  directionLo := (320711914740977932297/100000000000000000000)
  directionHi := (160355957370488966149/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree044.table
  base := (-358591212597908623858660828087982591919/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-15723551196880705900921216059375000000000000)
      constant := (106878516437557312734773638454525954640311350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree044.table
  base := (-719273278931735581339953969555567656887/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-16068058267626892200580224578175000000000000)
      constant := (112318808227687495859252351250463071036974275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320711914740977932297/100000000000000000000)
  centralHi := (160355957370488966149/50000000000000000000)
  directionLo := (324419690112305603731/100000000000000000000)
  directionHi := (81104922528076400933/25000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree045.table
  base := (-226807504861732248510564058959560390231/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-5372983785874495967979647248575000000000000)
      constant := (37666047065949701969732905667904963777859280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree045.table
  base := (-3638627685809158880936489720338422499337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-5490429378174332206499763789075000000000000)
      constant := (39569092483661451356075579836510979488458035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (324419690112305603731/100000000000000000000)
  centralHi := (81104922528076400933/25000000000000000000)
  directionLo := (328085565681126084907/100000000000000000000)
  directionHi := (82021391420281521227/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree046.table
  base := (-7338096471181492865787199975421052962299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-33028703036732539813913334864150000000000000)
      constant := (238573718681173253597420688086409735408433835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree046.table
  base := (-3678061745104635606096373819285770410531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-16874518001419101038418358156275000000000000)
      constant := (125270875964726768462238088805146185270348115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (328085565681126084907/100000000000000000000)
  centralHi := (82021391420281521227/25000000000000000000)
  directionLo := (41463866325852885271/12500000000000000000)
  directionHi := (331710930606823082169/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree047.table
  base := (-1853197290754968201437619483430941417783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-16909751679109051909974393118425000000000000)
      constant := (125744246113272051030820404001133737907821390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree047.table
  base := (-7429526047563190783040910435581848451567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-34555495736630410914674849890650000000000000)
      constant := (264018388645609133110586041530212686962457055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41463866325852885271/12500000000000000000)
  centralHi := (331710930606823082169/100000000000000000000)
  directionLo := (335297098943287456223/100000000000000000000)
  directionHi := (10478034341977733007/3125000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree048.table
  base := (-7482094898619686379387651729958384570501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-11536767893234555941994745869850000000000000)
      constant := (88246612392690681796340066537410134295626055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree048.table
  base := (-1874408264585370538710595494038312091593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-5893659245070436625418830578125000000000000)
      constant := (46307288006146383845023511327109278055296230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335297098943287456223/100000000000000000000)
  centralHi := (10478034341977733007/3125000000000000000)
  directionLo := (16942265760187212793/5000000000000000000)
  directionHi := (338845315203744255861/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree049.table
  base := (-471635814157012535569083647106397117251/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-17700552000594615916009844491125000000000000)
      constant := (139163531379937020605413089133240147973735320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree049.table
  base := (-1890149403878274162648043642787216524223/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-18084207602107414295175558523425000000000000)
      constant := (146008553222620321408978939270014832734986590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16942265760187212793/5000000000000000000)
  centralHi := (338845315203744255861/100000000000000000000)
  directionLo := (342356759406419341279/100000000000000000000)
  directionHi := (2139729746290120883/625000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree050.table
  base := (-7605167343836138367623324699977666033249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-36191904322674795838055140354950000000000000)
      constant := (292249545611353725353618467775096817745865585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree050.table
  base := (-3809278822119018977223166354204094810007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-18487437469003518714094625312475000000000000)
      constant := (153268962982563768191610010203775248998619655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342356759406419341279/100000000000000000000)
  centralHi := (2139729746290120883/625000000000000000)
  directionLo := (34583255165904351011/10000000000000000000)
  directionHi := (345832551659043510111/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree051.table
  base := (-3829603838427250437823372512025005833931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 425000000000000000000000000000000000000000
      center := (1078)
      previous := (707)
      next := (0)
      square := (9787132691653019876676378375000000000000)
      linear := (-362575535727062351412652860075000000000000)
      constant := (3004967871918244980841571677857874504115865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree051.table
  base := (-7671637467149374285162426646752171276417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (2128)
      previous := (1442)
      next := (0)
      square := (19574265383306039753352756750000000000000)
      linear := (-740810483760769534627987925550000000000000)
      constant := (6302071522704404569364969146926065441504555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34583255165904351011/10000000000000000000)
  centralHi := (345832551659043510111/100000000000000000000)
  directionLo := (349273756332686836523/100000000000000000000)
  directionHi := (87318439083171709131/25000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree052.table
  base := (-3854205647406297685402363364194367645333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-18886752482822961925063021550175000000000000)
      constant := (160549043185308711119484720537997416257481445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree052.table
  base := (-1929987300491246410508176753625811036933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-19293897202795727551932758890575000000000000)
      constant := (168309892746662461492103095161644218309790890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349273756332686836523/100000000000000000000)
  centralHi := (87318439083171709131/25000000000000000000)
  directionLo := (70536277173801906853/20000000000000000000)
  directionHi := (176340692934504767133/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree053.table
  base := (-484555260954704852906229131028798774739/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-19282152643565743928080747236525000000000000)
      constant := (168011588251739689034303234844871258492051480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree053.table
  base := (-60653078202929260856094239619231395913/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-19697127069691831970851825679625000000000000)
      constant := (176089950468567969093895794345680441517897280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70536277173801906853/20000000000000000000)
  centralHi := (176340692934504767133/50000000000000000000)
  directionLo := (356056404259529220397/100000000000000000000)
  directionHi := (178028202129764610199/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree054.table
  base := (-1948180534263508308677796595385861273737/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-6559184268102841977032824307625000000000000)
      constant := (58546929659949844292269955029964860918900070) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree054.table
  base := (-1950665802960935846759484069133856895419/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-6700118978862645463256964156225000000000000)
      constant := (61347599685712852518098774611413153572239090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356056404259529220397/100000000000000000000)
  centralHi := (178028202129764610199/50000000000000000000)
  directionLo := (179699865115395535961/50000000000000000000)
  directionHi := (359399730230791071923/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree055.table
  base := (-3914005927519781712035977767572488927339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-20072952965051307934116198609225000000000000)
      constant := (183436457501812647603893303488173260499985435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree055.table
  base := (-7837239285304843826822622599658675051609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-41007173606968081617379918515450000000000000)
      constant := (384336519483773886472484729429579643651274985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179699865115395535961/50000000000000000000)
  centralHi := (359399730230791071923/100000000000000000000)
  directionLo := (181356120082632928143/50000000000000000000)
  directionHi := (362712240165265856287/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree056.table
  base := (-7858831769665399411904488019768005560311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-40936706251588179874267848591150000000000000)
      constant := (382796847595978708690713999884465695896051815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree056.table
  base := (-393369837883952245693151253746558455593/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-20906816670380145227609026046775000000000000)
      constant := (200466170984845296030550518793486690950043450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181356120082632928143/50000000000000000000)
  centralHi := (362712240165265856287/100000000000000000000)
  directionLo := (365994770784290848243/100000000000000000000)
  directionHi := (91498692696072712061/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree057.table
  base := (-3942626451159338296596651258483768183493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-6954584428845623980050549993975000000000000)
      constant := (66508844643174345710857336736600954974852615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree057.table
  base := (-789320300469217504834972307496142151111/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-7103348845758749882176030945275000000000000)
      constant := (69645462249709294293269235093400372958223025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (365994770784290848243/100000000000000000000)
  centralHi := (91498692696072712061/25000000000000000000)
  directionLo := (73849624323265368337/20000000000000000000)
  directionHi := (184624060808163420843/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree058.table
  base := (-7907339586764493117083960067137452634293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-42518306894559307886338751336550000000000000)
      constant := (415641296905955691454530661471659142830339845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree058.table
  base := (-7914718965779390381405076300849726092757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-43426552808344708130894319249750000000000000)
      constant := (435157549897018005652912419045596437387898405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73849624323265368337/20000000000000000000)
  centralHi := (184624060808163420843/50000000000000000000)
  directionLo := (372473057271161289253/100000000000000000000)
  directionHi := (186236528635580644627/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree059.table
  base := (-990643765692718932730944316917334703059/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-21654553608022435946187101354625000000000000)
      constant := (216280640997600709007784365567793416248956940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree059.table
  base := (-1982999946230758186359374959210430582761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-22116506271068458484366226413925000000000000)
      constant := (226393216058406929948750791826175566847462130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (372473057271161289253/100000000000000000000)
  centralHi := (186236528635580644627/50000000000000000000)
  directionLo := (187835154769192432001/50000000000000000000)
  directionHi := (375670309538384864003/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree060.table
  base := (-3969368689652378261622858992529271594827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-7349984589588405983068275680325000000000000)
      constant := (74968798995974473704188592402695202545474985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree060.table
  base := (-993136923132667574335689058239205146219/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-7506578712654854301095097734325000000000000)
      constant := (78459867290284344132376487576077394254854180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187835154769192432001/50000000000000000000)
  centralHi := (375670309538384864003/100000000000000000000)
  directionLo := (378840579326457579121/100000000000000000000)
  directionHi := (189420289663228789561/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree061.table
  base := (-1589629859242353312501301833188724762423/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-44890707859015999904445105454650000000000000)
      constant := (467395624992625914520795496633694390774481475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree061.table
  base := (-7954050983211026728158785618655942365887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-45845932009721334644408719984050000000000000)
      constant := (489075668755927170359477518806326489843879855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (378840579326457579121/100000000000000000000)
  centralHi := (189420289663228789561/50000000000000000000)
  directionLo := (76396907691383974669/20000000000000000000)
  directionHi := (190992269228459936673/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree062.table
  base := (-3976714693843249877180547902646741732521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-22840754090250781955240278413675000000000000)
      constant := (242654793211758408307550472845156374589521465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree062.table
  base := (-7958907552654407643209753132471517691021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-46652391743513543482246853562150000000000000)
      constant := (507735649540298334577134563016795970809423965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76396907691383974669/20000000000000000000)
  centralHi := (190992269228459936673/50000000000000000000)
  directionLo := (96275707831689751493/25000000000000000000)
  directionHi := (385102831326759005973/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree063.table
  base := (-3977308578095052226328835293278915425451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-7745384750331187986086001366675000000000000)
      constant := (83925751170891745065685997717211967210223305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree063.table
  base := (-7959702237839544757438517262775493598531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-15819617159101917440028329046750000000000000)
      constant := (175579661691212403733977871603549411750122705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96275707831689751493/25000000000000000000)
  centralHi := (385102831326759005973/100000000000000000000)
  directionLo := (388196076450582248253/100000000000000000000)
  directionHi := (194098038225291124127/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree064.table
  base := (-7951748480029422175305701932673513537529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-47263108823472691922551459572750000000000000)
      constant := (522130231265666717877703072859140318814811785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree064.table
  base := (-3978234363509645306897183160441942619627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-24132655605548980578961560359175000000000000)
      constant := (273042764658683842230094754679164178743916955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (388196076450582248253/100000000000000000000)
  centralHi := (194098038225291124127/50000000000000000000)
  directionLo := (97816216973262668937/25000000000000000000)
  directionHi := (391264867893050675749/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree065.table
  base := (-3972427979841885449858159273508567938247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-24026954572479127964293455472725000000000000)
      constant := (270518308910693857816892481214390357987699255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree065.table
  base := (-7949237587103007105663035775973090338527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-49071770944890169995761254296450000000000000)
      constant := (565775149763937670544075083400956653382485455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97816216973262668937/25000000000000000000)
  centralHi := (391264867893050675749/100000000000000000000)
  directionLo := (15772391064038781181/4000000000000000000)
  directionHi := (197154888300484764763/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree066.table
  base := (-7933969229649224755581442462209861503909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-16281569822147939978207454106050000000000000)
      constant := (186757846075657660770049057666926750126851495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree066.table
  base := (-1984509141176226084789844797466796346661/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-8313038446447063138933231312425000000000000)
      constant := (97634621021962428107263741124670958558149710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15772391064038781181/4000000000000000000)
  centralHi := (197154888300484764763/50000000000000000000)
  directionLo := (198665675821747450057/50000000000000000000)
  directionHi := (79466270328698980023/20000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree067.table
  base := (-989889404921203493661493948705912775553/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-24817754893964691970328906845425000000000000)
      constant := (289920437828291726636042624414619472471910980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree067.table
  base := (-7922890856938258498802307428298689170521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-50684690412474587671437521452650000000000000)
      constant := (606183149191392326498822120796585182445791465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198665675821747450057/50000000000000000000)
  centralHi := (79466270328698980023/20000000000000000000)
  directionLo := (400330121368086287827/100000000000000000000)
  directionHi := (100082530342021571957/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree068.table
  base := (-7900318506441305854803644155162219364067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2550000000000000000000000000000000000000000
      center := (6468)
      previous := (4242)
      next := (0)
      square := (58722796149918119260058270250000000000000)
      linear := (-2966253535847938114511368533150000000000000)
      constant := (35278736695672885766088282623833634062162915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree068.table
  base := (-197595583877971649987702118826108452633/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1275000000000000000000000000000000000000000
      center := (3192)
      previous := (2163)
      next := (0)
      square := (29361398074959059630029135125000000000000)
      linear := (-1514445592537258720861048677375000000000000)
      constant := (18438274109086381372092120587406846891571700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (400330121368086287827/100000000000000000000)
  centralHi := (100082530342021571957/25000000000000000000)
  directionLo := (201653297239548501627/50000000000000000000)
  directionHi := (80661318895819400651/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree069.table
  base := (-393880067246913483767578849240743896147/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-8536185071816751992121452739375000000000000)
      constant := (103327731000838159666394978164601250700675850) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree069.table
  base := (-3940427432099190549410915740013386380143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-8716268313343167557852298101475000000000000)
      constant := (107993691249157177982342381284040656680693365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201653297239548501627/50000000000000000000)
  centralHi := (80661318895819400651/20000000000000000000)
  directionLo := (203130630522618927691/50000000000000000000)
  directionHi := (406261261045237855383/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree070.table
  base := (-7850984071401911949333064731969652526723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-52007910752386075958764167808950000000000000)
      constant := (640524374120146216542740082954211556296655795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree070.table
  base := (-7854004300443719937987883927274247616589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-53104069613851214184951922186950000000000000)
      constant := (669365550547393548755294486055166136582086685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203130630522618927691/50000000000000000000)
  centralHi := (406261261045237855383/100000000000000000000)
  directionLo := (204597296720782088947/50000000000000000000)
  directionHi := (81838918688312835579/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree071.table
  base := (-156409703815391203208525309078528590681/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-26399355536935819982399809590825000000000000)
      constant := (330706203976443759507433315663294463984946625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree071.table
  base := (-3911644434804063279404760870082417306717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-26955264673821711511395027882525000000000000)
      constant := (345555727139674048156817738880942720975381805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204597296720782088947/50000000000000000000)
  centralHi := (81838918688312835579/20000000000000000000)
  directionLo := (206053523615556679753/50000000000000000000)
  directionHi := (412107047231113359507/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree072.table
  base := (-7786121564276076299233184269272951133759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-17863170465119067990278356851450000000000000)
      constant := (227543471469933246228496607305220585611718245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree072.table
  base := (-7788724227598924687234514112209221353647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-18238996360478543953542729781050000000000000)
      constant := (237733263607482820739031227790177675143980085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206053523615556679753/50000000000000000000)
  centralHi := (412107047231113359507/100000000000000000000)
  directionLo := (414999061990852212133/100000000000000000000)
  directionHi := (207499530995426106067/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree073.table
  base := (-1936977140287166780200285790890259305569/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-27190155858421383988435260963525000000000000)
      constant := (352089163432641467135739756957031451820716770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree073.table
  base := (-7750324625433010022985225079000892545661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-55523448815227840698466322921250000000000000)
      constant := (735630498398536403607372654786811130814559565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414999061990852212133/100000000000000000000)
  centralHi := (207499530995426106067/50000000000000000000)
  directionLo := (417871062086174252939/100000000000000000000)
  directionHi := (20893553104308712647/5000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree074.table
  base := (-96323252446553549374963625914679854643/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-27585556019164165991452986649875000000000000)
      constant := (363028042283593210889768744008784513204903800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree074.table
  base := (-7708103040080753901301628526690806581037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-56329908549020049536304456499350000000000000)
      constant := (758403520752445360746207105214255353471204605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417871062086174252939/100000000000000000000)
  centralHi := (20893553104308712647/5000000000000000000)
  directionLo := (105180864349452663747/25000000000000000000)
  directionHi := (420723457397810654989/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree075.table
  base := (-7659989251448854990852296385996315878987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-18653970786604631996313808224150000000000000)
      constant := (249421210699757367481729394253235323554863785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree075.table
  base := (-1532414258525904390406036350872679324557/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-19045456094270752791380863359150000000000000)
      constant := (260506268879920534542737547420444891880075675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105180864349452663747/25000000000000000000)
  centralHi := (420723457397810654989/100000000000000000000)
  directionLo := (16942265760187212793/4000000000000000000)
  directionHi := (211778322002340159913/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree076.table
  base := (-3805153696532906806490518915050659900759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-28376356340649729997488438022575000000000000)
      constant := (385400459447438596305576856429635389330209735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree076.table
  base := (-7612240155047100265981385724157194114823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-57942828016604467211980723655550000000000000)
      constant := (804976309364004779549725744257178563512242295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16942265760187212793/4000000000000000000)
  centralHi := (211778322002340159913/50000000000000000000)
  directionLo := (106592751206474987097/25000000000000000000)
  directionHi := (426371004825899948389/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree077.table
  base := (-7556825268165929265375760583243842918451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-57543513002785024001012327417850000000000000)
      constant := (793667898796695706716051824135697940948514915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree077.table
  base := (-7558619446690878033557812918580303164429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-58749287750396676049818857233650000000000000)
      constant := (828775986358260606370351259490114385782200285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106592751206474987097/25000000000000000000)
  centralHi := (426371004825899948389/100000000000000000000)
  directionLo := (42916691022490037383/10000000000000000000)
  directionHi := (429166910224900373831/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree078.table
  base := (-7499552599149509716174221112945645926087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-19444771108090196002349259596850000000000000)
      constant := (272288176552707436861668447434093541636804285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree078.table
  base := (-1500243624317762245788653071112420635799/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-19851915828062961629218996937250000000000000)
      constant := (284305932935605964980667468737472760906352225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42916691022490037383/10000000000000000000)
  centralHi := (429166910224900373831/100000000000000000000)
  directionLo := (107986179644586868367/25000000000000000000)
  directionHi := (431944718578347473469/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree079.table
  base := (-232453070829500750414831820483930547587/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-29562556822878076006541615081625000000000000)
      constant := (420195386491035212947687787701874577219365680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree079.table
  base := (-116250692928302349134399413189329493093/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-30181103608990546862747562194925000000000000)
      constant := (438700855651412621189924263643006212718139040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107986179644586868367/25000000000000000000)
  centralHi := (431944718578347473469/100000000000000000000)
  directionLo := (217352388406170899939/50000000000000000000)
  directionHi := (434704776812341799879/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree080.table
  base := (-3686835192261837457019429789529343411137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-29957956983620858009559340767975000000000000)
      constant := (432123296796797441846999327065990296312721105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree080.table
  base := (-7375105576958207456200497787952931444783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-61168666951773302563333257967950000000000000)
      constant := (902227691538395896835869737438824042186865695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217352388406170899939/50000000000000000000)
  centralHi := (434704776812341799879/100000000000000000000)
  directionLo := (437447420908168113209/100000000000000000000)
  directionHi := (43744742090816811321/10000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree081.table
  base := (-1461015273878233431035333103041153254763/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-20235571429575760008384710969550000000000000)
      constant := (296143986447674486315745980138747667734337325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree081.table
  base := (-7306408612898780571856752650919098825193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-20658375561855170467057130515350000000000000)
      constant := (309131903341319339314960074464021902197596115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437447420908168113209/100000000000000000000)
  centralHi := (43744742090816811321/10000000000000000000)
  directionLo := (55021622047460251277/12500000000000000000)
  directionHi := (440172976379682010217/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree082.table
  base := (-723272300170475480184536653451159309153/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-30748757305106422015594792140675000000000000)
      constant := (456473420418318060141318203333276121974108725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree082.table
  base := (-3616979833214554567481233421258767092749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-31390793209678860119504762562075000000000000)
      constant := (476452869916988387359887529535773244652933085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55021622047460251277/12500000000000000000)
  centralHi := (440172976379682010217/100000000000000000000)
  directionLo := (442881758724253845111/100000000000000000000)
  directionHi := (55360219840531730639/12500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree083.table
  base := (-7156616482664613236627409504512615919061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-62288314931698408037225035654050000000000000)
      constant := (937791211192230107416699145712137809990870565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree083.table
  base := (-894720551305049482463565766425005153957/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-31794023076574964538423829351125000000000000)
      constant := (489378878188234401697268377335080410630385620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (442881758724253845111/100000000000000000000)
  centralHi := (55360219840531730639/12500000000000000000)
  directionLo := (111393518462259591877/25000000000000000000)
  directionHi := (445574073849038367509/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree084.table
  base := (-7076762485310786299195518499771974498579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-21026371751061324014420162342250000000000000)
      constant := (320988348605725610101481632896589496849553345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree084.table
  base := (-3538914013866751631541939817573293807177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-10732417647823689652447632046725000000000000)
      constant := (167491956197332060826336369293866590448629235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111393518462259591877/25000000000000000000)
  centralHi := (445574073849038367509/100000000000000000000)
  directionLo := (56031277309275051003/12500000000000000000)
  directionHi := (17930008738968016321/4000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree085.table
  base := (-699316620102962218710613149873180442983/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1275000000000000000000000000000000000000000
      center := (3234)
      previous := (2121)
      next := (0)
      square := (29361398074959059630029135125000000000000)
      linear := (-1878526928666751060273409952925000000000000)
      constant := (29072597711965190279690191381261694935196675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree085.table
  base := (-6994155254759625902034210267253338316729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2550000000000000000000000000000000000000000
      center := (6384)
      previous := (4326)
      next := (0)
      square := (58722796149918119260058270250000000000000)
      linear := (-3835350918866726279560230932850000000000000)
      constant := (60675744807295972412109406289450398729234105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56031277309275051003/12500000000000000000)
  centralHi := (17930008738968016321/4000000000000000000)
  directionLo := (450910480514601142633/100000000000000000000)
  directionHi := (225455240257300571317/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree086.table
  base := (-6905832381816035678651485371895873505681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-64660715896155100055331389772150000000000000)
      constant := (1014301019761251069467867123697891388352872865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree086.table
  base := (-690675042131884844865182370887649374623/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-33003712677263277795181029718275000000000000)
      constant := (529182755613451467242270841507360199805046475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (450910480514601142633/100000000000000000000)
  centralHi := (225455240257300571317/50000000000000000000)
  directionLo := (453555139441334736479/100000000000000000000)
  directionHi := (2834719621508342103/625000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree087.table
  base := (-6814765378694499041682101077247982054389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-21817172072546888020455613714950000000000000)
      constant := (346821039872929847632838246847296665931407895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree087.table
  base := (-851952185825612686043740636345434299293/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-11135647514719794071366698835775000000000000)
      constant := (180930878088250292217716216633933389750086460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (453555139441334736479/100000000000000000000)
  centralHi := (2834719621508342103/625000000000000000)
  directionLo := (228092233312200207769/50000000000000000000)
  directionHi := (456184466624400415539/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree088.table
  base := (-1343993835332363641064776044280917463429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-66242316539126228067402292517550000000000000)
      constant := (1066954604504470736098648574030211113980176425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree088.table
  base := (-6720760071945567485347748827860355936749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-67620344822110973266038326592750000000000000)
      constant := (1113146917933372050488736376098505357014193085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228092233312200207769/50000000000000000000)
  centralHi := (456184466624400415539/100000000000000000000)
  directionLo := (114699681414424817/25000000000000000)
  directionHi := (458798725657699268001/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree089.table
  base := (-413840464154937735483978200652440670507/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-33516558430305896036718871945125000000000000)
      constant := (546887729296122834062607711511263357546817240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree089.table
  base := (-1324436298110675380164548990835732738273/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-68426804555903182103876460170850000000000000)
      constant := (1141050445075737506482654666001995492897932725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114699681414424817/25000000000000000)
  centralHi := (458798725657699268001/100000000000000000000)
  directionLo := (461398172667457468961/100000000000000000000)
  directionHi := (230699086333728734481/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree090.table
  base := (-407450217100466345534025723301171015491/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-11303986197016226013245532543825000000000000)
      constant := (186820944563256524139489382205488463060924040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree090.table
  base := (-6519884774570032042480928887355852842709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-23077754763231796980571531249650000000000000)
      constant := (389765278937421280594715530892870792642285495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (461398172667457468961/100000000000000000000)
  centralHi := (230699086333728734481/50000000000000000000)
  directionLo := (231991528302548688423/50000000000000000000)
  directionHi := (463983056605097376847/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree091.table
  base := (-6413240384555915699546206070413797931997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-68614717503582920085508646635650000000000000)
      constant := (1148405217573035846775571290618716185964793005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree091.table
  base := (-6413872699660015565182804520094560447489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-70039724023487599779552727327050000000000000)
      constant := (1197883081110445524084391871753490080460135185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231991528302548688423/50000000000000000000)
  centralHi := (463983056605097376847/100000000000000000000)
  directionLo := (233276809762752187131/50000000000000000000)
  directionHi := (466553619525504374263/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree092.table
  base := (-1260712194175718702663900700563402995213/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-69405517825068484091544098008350000000000000)
      constant := (1176214096984648198887927432933648240078758225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree092.table
  base := (-6304147807383736407534241393072959810489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-70846183757279808617390860905150000000000000)
      constant := (1226812166952618180634534058767788719221530185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233276809762752187131/50000000000000000000)
  centralHi := (466553619525504374263/100000000000000000000)
  directionLo := (23455504842578489919/5000000000000000000)
  directionHi := (469110096851569798381/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree093.table
  base := (-3095083905520967062323692396146353715527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-11699386357759008016263258230175000000000000)
      constant := (200725382406120697906336677396618518881063485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree093.table
  base := (-6190712425558031298259140008333492914813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-23884214497024005818409664827750000000000000)
      constant := (418694361415898608071851681681718102738095215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23455504842578489919/5000000000000000000)
  centralHi := (469110096851569798381/100000000000000000000)
  directionLo := (235826358812914134571/50000000000000000000)
  directionHi := (471652717625828269143/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree094.table
  base := (-6073063270356162536546323076157427378737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-70987118468039612103615000753750000000000000)
      constant := (1232819799675643987037772773906637552313175105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree094.table
  base := (-6073568686791601608687204188737187456667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-72459103224864226293067128061350000000000000)
      constant := (1285695823750819734382740564513484292375348555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235826358812914134571/50000000000000000000)
  centralHi := (471652717625828269143/100000000000000000000)
  directionLo := (474181704749950676949/100000000000000000000)
  directionHi := (9483634094999013539/2000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree095.table
  base := (-186007797473413926008165565999510083969/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-35888959394762588054825226063225000000000000)
      constant := (630808301646517930624159287132673980575910160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree095.table
  base := (-5952718545364780093884599876467460901473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-73265562958656435130905261639450000000000000)
      constant := (1315650376990184668642878787813413556992114545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474181704749950676949/100000000000000000000)
  centralHi := (9483634094999013539/2000000000000000000)
  directionLo := (14896789850400049529/3125000000000000000)
  directionHi := (476697275212801584929/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree096.table
  base := (-728466068667975449851363653307253438687/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-12094786518501790019280983916525000000000000)
      constant := (215123782775652541926488639562444075124389140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree096.table
  base := (-728520474075834177066249778876560901723/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-12345337115408107328123899202925000000000000)
      constant := (224324456033396491602209612578093477988041060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14896789850400049529/3125000000000000000)
  centralHi := (476697275212801584929/100000000000000000000)
  directionLo := (479199640307721429229/100000000000000000000)
  directionHi := (47919964030772142923/10000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree097.table
  base := (-5699502189582290977481666100052149793371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-73359519432496304121721354871850000000000000)
      constant := (1320198071831117117533135543769733930645736715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree097.table
  base := (-712488258863502672494404508283778331917/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-37439241213120426403290764397825000000000000)
      constant := (688292447130819360123216857445339283724559220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479199640307721429229/100000000000000000000)
  centralHi := (47919964030772142923/10000000000000000000)
  directionLo := (481689005839649298789/100000000000000000000)
  directionHi := (48168900583964929879/10000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree098.table
  base := (-1391893029758003277027900841248300280327/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-37075159876990934063878403122275000000000000)
      constant := (674991360772725595261365906659927236569564910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree098.table
  base := (-1113589377298976117126919638843398033263/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-75684942160033061644419662373750000000000000)
      constant := (1407564844644474025175015881419849347629024475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481689005839649298789/100000000000000000000)
  centralHi := (48168900583964929879/10000000000000000000)
  directionLo := (96833114464532182831/20000000000000000000)
  directionHi := (121041393080665228539/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree099.table
  base := (-2715969939994575158166941689398471877639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-12490186679244572022298709602875000000000000)
      constant := (230016106518510588136016814534199208136811645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree099.table
  base := (-2716143810538162741623505055598719973589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-12748566982304211747042965991975000000000000)
      constant := (239814430226529337776607672171569849638163895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96833114464532182831/20000000000000000000)
  centralHi := (121041393080665228539/25000000000000000000)
  directionLo := (486629535168458405597/100000000000000000000)
  directionHi := (243314767584229202799/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree100.table
  base := (-2646303444694892439043460853142824113049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-37865960198476498069913854494975000000000000)
      constant := (705269909192768107873524866976125857469932585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree100.table
  base := (-5292929542468626757545483392181479654323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-77297861627617479320095929529950000000000000)
      constant := (1470550098909761191281919864541893285698509795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486629535168458405597/100000000000000000000)
  centralHi := (243314767584229202799/50000000000000000000)
  directionLo := (97816216973262668937/20000000000000000000)
  directionHi := (244540542433156672343/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree101.table
  base := (-514957444932584039816979972135954263177/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-38261360359219280072931580181325000000000000)
      constant := (720656126862150381244387167902583191345638525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree101.table
  base := (-6437342267860867080770618753939612577/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-39052160680704844078967031554025000000000000)
      constant := (751277696125975108708351249154868711791482000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97816216973262668937/20000000000000000000)
  centralHi := (244540542433156672343/50000000000000000000)
  directionLo := (24576020357746598357/5000000000000000000)
  directionHi := (491520407154931967141/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree102.table
  base := (-5002843756654738720893679828551656137607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (2156)
      previous := (1414)
      next := (0)
      square := (19574265383306039753352756750000000000000)
      linear := (-1515951392939688708860757092850000000000000)
      constant := (28870861567430985202866388308633109228303405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree102.table
  base := (-200124860192033773486630814764571874401/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (2128)
      previous := (1442)
      next := (0)
      square := (19574265383306039753352756750000000000000)
      linear := (-1547270217552978372466121503650000000000000)
      constant := (30096126603035633058014012051285284766897875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24576020357746598357/5000000000000000000)
  centralHi := (491520407154931967141/100000000000000000000)
  directionLo := (246973841593340708637/50000000000000000000)
  directionHi := (19757907327467256691/4000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree103.table
  base := (-970483182356671304941765364004554400687/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-78104321361409688157934063108050000000000000)
      constant := (1503844872259310853918202239883601283365109275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree103.table
  base := (-303292099687068681355470038740218340423/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-39858620414497052916805165132125000000000000)
      constant := (783795644082889664829801904105879227954130360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246973841593340708637/50000000000000000000)
  centralHi := (19757907327467256691/4000000000000000000)
  directionLo := (496363089684587945429/100000000000000000000)
  directionHi := (49636308968458794543/10000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree104.table
  base := (-1174572981674858362698579442932619579511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-39447560841447626081984757240375000000000000)
      constant := (767802523149162868430156172555414188245639630) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree104.table
  base := (-2349265492976043757886987486672476188441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-40261850281393157335724231921175000000000000)
      constant := (800310941289312903393103882719154815723108265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496363089684587945429/100000000000000000000)
  centralHi := (49636308968458794543/10000000000000000000)
  directionLo := (498766799092492117737/100000000000000000000)
  directionHi := (249383399546246058869/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree105.table
  base := (-908094546463373279093285655692643122023/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-26561974001460272056668321951150000000000000)
      constant := (522564819340171050375661688239520653443383825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree105.table
  base := (-283793406599953211166843867535964518381/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-13555026716096420584881099570075000000000000)
      constant := (272332372734052878289967024843384250167515640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (498766799092492117737/100000000000000000000)
  centralHi := (249383399546246058869/50000000000000000000)
  directionLo := (100231795943744417367/20000000000000000000)
  directionHi := (125289744929680521709/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree106.table
  base := (-4378959185195249174976535837256317017137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-80476722325866380176040417226150000000000000)
      constant := (1600113103712687257524770677257153865730711105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree106.table
  base := (-4379164914845219832155430790866381858371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-82136620030370732347124730998550000000000000)
      constant := (1667708346344306140323764895914894234643961715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100231795943744417367/20000000000000000000)
  centralHi := (125289744929680521709/25000000000000000000)
  directionLo := (62942474484202959093/12500000000000000000)
  directionHi := (100707959174724734549/20000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree107.table
  base := (-168550082947540770833236782332809841619/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-81267522647351944182075868598850000000000000)
      constant := (1632860979957333737071339462783841733414540875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree107.table
  base := (-842788582642801719723456139184113205073/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-82943079764162941184962864576650000000000000)
      constant := (1701764209366155810381554781173044346280042725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62942474484202959093/12500000000000000000)
  centralHi := (100707959174724734549/20000000000000000000)
  directionLo := (2529547040006326389/500000000000000000)
  directionHi := (505909408001265277801/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree108.table
  base := (-1011213030893149128940883828076237416151/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-13676387161472918031351886661925000000000000)
      constant := (277656347268035662881964953766559673867323610) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree108.table
  base := (-4045029143983947257700989847798607236623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-27916513165985050007600332718250000000000000)
      constant := (578720607560418240395135554170691012543079765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2529547040006326389/500000000000000000)
  centralHi := (505909408001265277801/100000000000000000000)
  directionLo := (50826797280561638379/10000000000000000000)
  directionHi := (508267972805616383791/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree109.table
  base := (-3872260003197391018203301890757953705681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-82849123290323072194146771344250000000000000)
      constant := (1699344411768031117866082093742344270685872865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree109.table
  base := (-3872424198887958307629836043610828214773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-84555999231747358860639131732850000000000000)
      constant := (1770901183724440653705522630681507059688959045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50826797280561638379/10000000000000000000)
  centralHi := (508267972805616383791/100000000000000000000)
  directionLo := (255307821685740219611/50000000000000000000)
  directionHi := (510615643371480439223/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree110.table
  base := (-1847988164102236625975621942555935284443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-41819961805904318100091111358475000000000000)
      constant := (866539980883989475395144567304470020541939595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree110.table
  base := (-3696128622411930836884919734676568647217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-85362458965539567698477265310950000000000000)
      constant := (1805982290135367278743337115224877074914314305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255307821685740219611/50000000000000000000)
  centralHi := (510615643371480439223/100000000000000000000)
  directionLo := (6411907116005577953/1250000000000000000)
  directionHi := (512952569280446236241/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree111.table
  base := (-879000416461999168659415078068655998591/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-14071787322215700034369612348275000000000000)
      constant := (294524121858168453470930583160141584164072010) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree111.table
  base := (-109879466116450587921445809804715089171/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-14361486449888629422719233148175000000000000)
      constant := (306900856623576707474580551299764987138366480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6411907116005577953/1250000000000000000)
  centralHi := (512952569280446236241/100000000000000000000)
  directionLo := (257639448361053152471/50000000000000000000)
  directionHi := (515278896722106304943/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree112.table
  base := (-666467307790621062511749472063152822353/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-85221524254779764212253125462350000000000000)
      constant := (1801538717644679428617971176322791162575498725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree112.table
  base := (-3332467540283711276375648872855229085819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-86975378433123985374153532467150000000000000)
      constant := (1877169730542323879034148616846732581912974635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257639448361053152471/50000000000000000000)
  centralHi := (515278896722106304943/100000000000000000000)
  directionLo := (103518953720155266201/20000000000000000000)
  directionHi := (258797384300388165503/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree113.table
  base := (-3144981429543012057432983063733239803531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-86012324576265328218288576835050000000000000)
      constant := (1836261919165414446281852564415216405451693115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree113.table
  base := (-3145102921109436966370546719756335658829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-87781838166916194211991666045250000000000000)
      constant := (1913276060695472080711889274772136284918976285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103518953720155266201/20000000000000000000)
  centralHi := (258797384300388165503/50000000000000000000)
  directionLo := (259950162318968025517/50000000000000000000)
  directionHi := (103980064927587210207/20000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree114.table
  base := (-2953936782163167930575131127197495420363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-28934374965916964074774676069250000000000000)
      constant := (623771444594703747879942720859459619117575465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree114.table
  base := (-369256181226906267129438143096943735371/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-14764716316784733841638299937225000000000000)
      constant := (324954021417211388115250496001209665209555620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259950162318968025517/50000000000000000000)
  centralHi := (103980064927587210207/20000000000000000000)
  directionLo := (522195701470599426091/100000000000000000000)
  directionHi := (130548925367649856523/25000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree115.table
  base := (-1379601503464215634074285701170582988091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-43796962609618228115179739790225000000000000)
      constant := (953347979861460954902314859577725522746625515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree115.table
  base := (-689826871839192839520765284609833232349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-44697378817250305943833966600725000000000000)
      constant := (993256966200485003901642936349082745875534170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (522195701470599426091/100000000000000000000)
  centralHi := (130548925367649856523/25000000000000000000)
  directionLo := (524481032745810070613/100000000000000000000)
  directionHi := (262240516372905035307/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree116.table
  base := (-640195120579216089195202774217327817197/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-44192362770361010118197465476575000000000000)
      constant := (971203397670572022381863495200515767824902010) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree116.table
  base := (-2560877366558803619638491492684475216939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-90201217368292820725506066779550000000000000)
      constant := (2023645470945781597085044889951812799934569435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524481032745810070613/100000000000000000000)
  centralHi := (262240516372905035307/50000000000000000000)
  directionLo := (526756449211446860231/100000000000000000000)
  directionHi := (65844556151430857529/12500000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree117.table
  base := (-2358669557731711613148361728227548186007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-29725175287402528080810127441950000000000000)
      constant := (659482279708038194656942432962331192871219885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree117.table
  base := (-2358759394427888876712395175030204149043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-30335892367361676521114733452550000000000000)
      constant := (687039580935609912387269693748001355004632865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526756449211446860231/100000000000000000000)
  centralHi := (65844556151430857529/12500000000000000000)
  directionLo := (529022078803514301397/100000000000000000000)
  directionHi := (264511039401757150699/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree118.table
  base := (-2152870555851228236642395861044549025663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-89966326183693148248465833698550000000000000)
      constant := (2014816089673023291136569911545671879973750895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree118.table
  base := (-134559615891905897659199278399518429273/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-45907068417938619200591166967875000000000000)
      constant := (1049466873377990446288736286024494700872812360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (529022078803514301397/100000000000000000000)
  centralHi := (264511039401757150699/50000000000000000000)
  directionLo := (265639023365041283359/50000000000000000000)
  directionHi := (531278046730082566719/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree119.table
  base := (-30365371481004900008357228937788154981/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1275000000000000000000000000000000000000000
      center := (3234)
      previous := (2121)
      next := (0)
      square := (29361398074959059630029135125000000000000)
      linear := (-2669327250152315066308861325625000000000000)
      constant := (60338663108693179043465321434787648655355040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree119.table
  base := (-1943461007633504461256358036110014097223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2550000000000000000000000000000000000000000
      center := (6384)
      previous := (4326)
      next := (0)
      square := (58722796149918119260058270250000000000000)
      linear := (-5448270386451143955236498089050000000000000)
      constant := (125711204803495842325111964558771946405208135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265639023365041283359/50000000000000000000)
  centralHi := (531278046730082566719/100000000000000000000)
  directionLo := (533524475552033034773/100000000000000000000)
  directionHi := (266762237776016517387/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree120.table
  base := (-1730209490048343461068008182163899289067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-30515975608888092086845578814650000000000000)
      constant := (696180735332460383030423404612373165527298185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree120.table
  base := (-1730281096082227273567042196966132819361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-31142352101153885358952867030650000000000000)
      constant := (725196315489996469131149804388183938076023355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533524475552033034773/100000000000000000000)
  centralHi := (266762237776016517387/50000000000000000000)
  directionLo := (535761485260756678243/100000000000000000000)
  directionHi := (133940371315189169561/25000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree121.table
  base := (-37833698909604372521634315949083168453/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-46169363574074920133286093908325000000000000)
      constant := (1062949534737080430261872360000144489295124900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree121.table
  base := (-94588396426861960224648227537963365643/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-47116758018626932457348367335025000000000000)
      constant := (1107214570110016121925835763722483430479500760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535761485260756678243/100000000000000000000)
  centralHi := (133940371315189169561/25000000000000000000)
  directionLo := (537989193352944679153/100000000000000000000)
  directionHi := (268994596676472339577/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree122.table
  base := (-1292799409422004736926449869230288866203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-93129527469635404272607639189350000000000000)
      constant := (2163585135104450318573551641433346697765009995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree122.table
  base := (-1292860954230595032129807419701523926243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-95039975771046073752534868248150000000000000)
      constant := (2253611062015011512267638756677053893779736595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537989193352944679153/100000000000000000000)
  centralHi := (268994596676472339577/50000000000000000000)
  directionLo := (540207714902603177649/100000000000000000000)
  directionHi := (10804154298052063553/2000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree123.table
  base := (-1068564067210584133897171571034553183919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-31306775930373656092881030187350000000000000)
      constant := (733866800647669395647316954746055070649237045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree123.table
  base := (-53431056057468326983107491780072021731/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-15974405917473047098395500304375000000000000)
      constant := (382189118504588102605355358592407959285987050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540207714902603177649/100000000000000000000)
  centralHi := (10804154298052063553/2000000000000000000)
  directionLo := (33901072664401065429/6250000000000000000)
  directionHi := (108483432526083409373/20000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree124.table
  base := (-840642131621218727782515160643986477457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-94711128112606532284678541934750000000000000)
      constant := (2239944869114722355696860811310888318620223905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree124.table
  base := (-84069502021638881619432177191554578663/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-48326447619315245714105567702175000000000000)
      constant := (1166500043245945638721794520688353054507479475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33901072664401065429/6250000000000000000)
  centralHi := (108483432526083409373/20000000000000000000)
  directionLo := (544617646970580999399/100000000000000000000)
  directionHi := (2723088234852904997/500000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree125.table
  base := (-60903378963700506469426729547341554651/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-47750964217046048145356996653725000000000000)
      constant := (1139309267904510550655443443745811371802939575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree125.table
  base := (-9516918984039486695492971119750787893/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-48729677486211350133024634491225000000000000)
      constant := (1186603593849561918341897733716268170703483040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544617646970580999399/100000000000000000000)
  centralHi := (2723088234852904997/500000000000000000)
  directionLo := (546809276135210141511/100000000000000000000)
  directionHi := (68351159516901267689/12500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree126.table
  base := (-373739214536861895405262344220758339113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-32097576251859220098916481560050000000000000)
      constant := (772540467091580103666476285264021004199981715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree126.table
  base := (-186892328477432410215552955438011512557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-16377635784369151517314567093425000000000000)
      constant := (402292668998731844552900593369042073364355135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (546809276135210141511/100000000000000000000)
  centralHi := (68351159516901267689/12500000000000000000)
  directionLo := (109798431235287254473/20000000000000000000)
  directionHi := (274496078088218136183/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree127.table
  base := (-26951713396620194046776447597122984503/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-97083529077063224302784896052850000000000000)
      constant := (2356953464815408863324856530540892359310897475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree127.table
  base := (-16850085825624023477141276157925704571/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-49536137220003558970862768069325000000000000)
      constant := (1227323282381400322575871133897251568282738860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109798431235287254473/20000000000000000000)
  centralHi := (274496078088218136183/50000000000000000000)
  directionLo := (275583195523145376309/50000000000000000000)
  directionHi := (551166391046290752619/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree128.table
  base := (107908003979460672285256411778838785189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-97874329398548788308820347425550000000000000)
      constant := (2396614725784917476425122348727461266133794315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree128.table
  base := (21573793156539518688926957245323334261/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-99878734173799326779563669716750000000000000)
      constant := (2495878839445552385856046897879572383270107175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275583195523145376309/50000000000000000000)
  centralHi := (551166391046290752619/100000000000000000000)
  directionLo := (553332082654469616177/100000000000000000000)
  directionHi := (276666041327234808089/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree129.table
  base := (88565090001380696224373638403692866773/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-16444188286672392052475966466375000000000000)
      constant := (406100863930589878954729560560616672384973970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree129.table
  base := (354224179275984146003595080425842786399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-33561731302530511872467267764950000000000000)
      constant := (845817612505468371364834208500135342826346555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553332082654469616177/100000000000000000000)
  centralHi := (276666041327234808089/50000000000000000000)
  directionLo := (17359041591377242177/3125000000000000000)
  directionHi := (111097866184814349933/20000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree130.table
  base := (604298372605753123757751054662168384807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-99455930041519916320891250170950000000000000)
      constant := (2476924837654272999957553147738660499948138345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree130.table
  base := (75533105193865046097597577095218634331/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-50745826820691872227619968436475000000000000)
      constant := (1289684279244217259591966057730881091119299540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17359041591377242177/3125000000000000000)
  centralHi := (111097866184814349933/20000000000000000000)
  directionLo := (557638233845396396347/100000000000000000000)
  directionHi := (139409558461349099087/25000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree131.table
  base := (171604384474305560576691303886898838079/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-100246730363005480326926701543650000000000000)
      constant := (2517573687479482270566915263522908532315362325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree131.table
  base := (214497712051359157842193899037460426809/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-51149056687587976646539035225525000000000000)
      constant := (1310813000954528814638259610137304781900434030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (557638233845396396347/100000000000000000000)
  centralHi := (139409558461349099087/25000000000000000000)
  directionLo := (55977888752788193643/10000000000000000000)
  directionHi := (559778887527881936431/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree132.table
  base := (557715449131168595090277188348851689979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-16839588447415174055493692152725000000000000)
      constant := (426425288762967746050222662580024090692019655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree132.table
  base := (17428157845770416899598997834232046619/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-17184095518161360355152700671525000000000000)
      constant := (444037527892883602261501037752914889835662560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55977888752788193643/10000000000000000000)
  centralHi := (559778887527881936431/100000000000000000000)
  directionLo := (140477846562565959213/25000000000000000000)
  directionHi := (561911386250263836853/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree133.table
  base := (1376525196950705634030622477273357156683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-101828331005976608338997604289050000000000000)
      constant := (2599858972501321010211049423593680003274220805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree133.table
  base := (688249256462885365539748542573304692499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-51955516421380185484377168803625000000000000)
      constant := (1353583027220648259189517379415695275841983165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140477846562565959213/25000000000000000000)
  centralHi := (561911386250263836853/100000000000000000000)
  directionLo := (564035822509025835089/100000000000000000000)
  directionHi := (56403582250902583509/10000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree134.table
  base := (41032618055497616307122362026616378651/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-51309565663731086172516527830875000000000000)
      constant := (1320747703416463177162970352889597640029041700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree134.table
  base := (16028124964653423748005393642813147/97656250000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-52358746288276289903296235592675000000000000)
      constant := (1375224331397986637180620569775839663602944000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (564035822509025835089/100000000000000000000)
  centralHi := (56403582250902583509/10000000000000000000)
  directionLo := (1415380717663037021/250000000000000000)
  directionHi := (566152287065214808401/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree135.table
  base := (477442346102533400126809908280984795469/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-17234988608157956058511417839075000000000000)
      constant := (447243505863991212142063199202332046058905410) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree135.table
  base := (1909746473974036503659589359945310959071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-35174650770114929548143534921150000000000000)
      constant := (931357664026983297801916681136020974335857595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1415380717663037021/250000000000000000)
  centralHi := (566152287065214808401/100000000000000000000)
  directionLo := (284130434494843184341/50000000000000000000)
  directionHi := (568260868989686368683/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree136.table
  base := (272739887488650315404769730243388993621/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1275000000000000000000000000000000000000000
      center := (3234)
      previous := (2121)
      next := (0)
      square := (29361398074959059630029135125000000000000)
      linear := (-3064727410895097069326587011975000000000000)
      constant := (80169289917409556539219057617688256773493420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree136.table
  base := (2181897872433878510148831842146584958987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2550000000000000000000000000000000000000000
      center := (6384)
      previous := (4326)
      next := (0)
      square := (58722796149918119260058270250000000000000)
      linear := (-6254730120243352793074631667150000000000000)
      constant := (166943473057564130485355166807347379164541685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284130434494843184341/50000000000000000000)
  centralHi := (568260868989686368683/100000000000000000000)
  directionLo := (71295206963355625133/12500000000000000000)
  directionHi := (114072331141369000213/20000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree137.table
  base := (491550758136816368610666407153878038233/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-104991532291918864363139409779850000000000000)
      constant := (2768379872518586119551012582635320306478700275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree137.table
  base := (2457734123323279703186983982973624856983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-107136871777929206320106871919650000000000000)
      constant := (2882346812192220907700592907327750663755021305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71295206963355625133/12500000000000000000)
  centralHi := (114072331141369000213/20000000000000000000)
  directionLo := (286227366518469759831/50000000000000000000)
  directionHi := (572454733036939519663/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree138.table
  base := (2737273383849985449887369498938759831539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-35260777537801476123058287050850000000000000)
      constant := (937111026949325105572646529564466507956573855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree138.table
  base := (2737255162663366919639737045096687796209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-35981110503907138385981668499250000000000000)
      constant := (975665434148164515530742676613424713865522005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286227366518469759831/50000000000000000000)
  centralHi := (572454733036939519663/100000000000000000000)
  directionLo := (574540185236971735613/100000000000000000000)
  directionHi := (287270092618485867807/50000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree139.table
  base := (94389931602310314568123900047341165757/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-53286566467444996187605156262625000000000000)
      constant := (1427307740942368015663002526568423583256905520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree139.table
  base := (755115232646507209995550787941601959083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-54374895622756811997891569537925000000000000)
      constant := (1485993756237939936177901407158383688985249610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (574540185236971735613/100000000000000000000)
  centralHi := (287270092618485867807/50000000000000000000)
  directionLo := (576618095040273510367/100000000000000000000)
  directionHi := (18019315470008547199/3125000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree140.table
  base := (826841752302491677389277007815689420261/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-53681966628187778190622881948975000000000000)
      constant := (1449113537676264787268308821498062027273662870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree140.table
  base := (1653675685507482009012384399792865697863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-54778125489652916416810636326975000000000000)
      constant := (1508660221021644559111042643110002072800236105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (576618095040273510367/100000000000000000000)
  centralHi := (18019315470008547199/3125000000000000000)
  directionLo := (578688543694804791681/100000000000000000000)
  directionHi := (289344271847402395841/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree141.table
  base := (719588183592702336275928154084477647709/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-36051577859287040129093738423550000000000000)
      constant := (980722620330859975338725535510080351004697525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree141.table
  base := (1798963215686287035119140324191642182641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-18393785118849673611909901038675000000000000)
      constant := (510499181819799565866412760970056922953916245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (578688543694804791681/100000000000000000000)
  centralHi := (289344271847402395841/50000000000000000000)
  directionLo := (580751611000222791959/100000000000000000000)
  directionHi := (14518790275005569799/2500000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree142.table
  base := (3892199481582416622398386571617061137317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-108945533899346684393316666643350000000000000)
      constant := (2986437838562334522627336763839819960030269195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree142.table
  base := (778437212462114362576976796924834773979/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-111169170446890250509297539810150000000000000)
      constant := (3109011458888479878343473052934605793725994825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580751611000222791959/100000000000000000000)
  centralHi := (14518790275005569799/2500000000000000000)
  directionLo := (582807375343770160271/100000000000000000000)
  directionHi := (36425460958985635017/6250000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree143.table
  base := (838028529514522295414659056674694937207/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-109736334220832248399352118016050000000000000)
      constant := (3031037007834231570679331997518224012763961725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree143.table
  base := (261883138591397008558950519492838547199/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-55987815090341229673567836694125000000000000)
      constant := (1577684772875668667254733553230401640816861320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (582807375343770160271/100000000000000000000)
  centralHi := (36425460958985635017/6250000000000000000)
  directionLo := (292427956867513906353/50000000000000000000)
  directionHi := (584855913735027812707/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree144.table
  base := (280735647914770764216880818654010101617/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-18421189090386302067564594898125000000000000)
      constant := (512660894765760877192402871768520356774692520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree144.table
  base := (4491758853215336294813168373546156719993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-37594029971491556061657935655450000000000000)
      constant := (1067356450439436411608537452270494196460389885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292427956867513906353/50000000000000000000)
  centralHi := (584855913735027812707/100000000000000000000)
  directionLo := (293448650919788006811/50000000000000000000)
  directionHi := (586897301839576013623/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree145.table
  base := (2398541296215554196026493059488176443077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-55658967431901688205711510380725000000000000)
      constant := (1560611460321220495257567398285531244880738795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree145.table
  base := (599633991062706168797393743498093043929/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-56794274824133438511405970272225000000000000)
      constant := (1624555437705683170721923808167956933381728860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293448650919788006811/50000000000000000000)
  centralHi := (586897301839576013623/100000000000000000000)
  directionLo := (147232903502901333979/25000000000000000000)
  directionHi := (588931614011605335917/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree146.table
  base := (5106079281347834806844517245596561907021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-112108735185288940417458472134150000000000000)
      constant := (3166809663788813281875642418872521095866936035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree146.table
  base := (2553034702302813504814687210040588254793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-57197504691029542930325037061275000000000000)
      constant := (1648247058931338124824815912368775950084527655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147232903502901333979/25000000000000000000)
  centralHi := (588931614011605335917/100000000000000000000)
  directionLo := (18467466353922414547/3125000000000000000)
  directionHi := (118191784665103453101/20000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree147.table
  base := (5418760392306389277138598866952136282351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-37633178502258168141164641168950000000000000)
      constant := (1070908532618533269173963069240065836927997195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree147.table
  base := (135468781124669324776983432030481453483/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-19200244852641882449748034616775000000000000)
      constant := (557369846418972651343788275828590914005658700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18467466353922414547/3125000000000000000)
  centralHi := (118191784665103453101/20000000000000000000)
  directionLo := (148244825401638111939/25000000000000000000)
  directionHi := (592979301606552447757/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree148.table
  base := (5735125886567383366209806680125183446631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-113690335828260068429529374879550000000000000)
      constant := (3258970722674865318580670448760942670241145385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree148.table
  base := (5735117415116902505701987928375455665107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-116007928849643503536326341278750000000000000)
      constant := (3392285757215165635622708842673787600308238845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148244825401638111939/25000000000000000000)
  centralHi := (592979301606552447757/100000000000000000000)
  directionLo := (594992819460482896263/100000000000000000000)
  directionHi := (74374102432560362033/12500000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree149.table
  base := (189224241486210901242277088881517398327/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-57240568074872816217782413126125000000000000)
      constant := (1652772519044034949628136389947212046747960720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree149.table
  base := (37844799264564451246219585850900253491/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-58407194291717856187082237428425000000000000)
      constant := (1720347076912529804144768191406572207910678800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (594992819460482896263/100000000000000000000)
  centralHi := (74374102432560362033/12500000000000000000)
  directionLo := (7462494328780036147/1250000000000000000)
  directionHi := (596999546302402891761/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree150.table
  base := (6378909880715967993374060089424630272987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-38423978823743732147200092541650000000000000)
      constant := (1117482847981792121766716476028718590744466215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree150.table
  base := (6378902615685912892054058504055543944527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-39206949439075973737334202811650000000000000)
      constant := (1163148089403129401489152776886860260999841515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7462494328780036147/1250000000000000000)
  centralHi := (596999546302402891761/100000000000000000000)
  directionLo := (598999550384651786537/100000000000000000000)
  directionHi := (299499775192325893269/50000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree151.table
  base := (26196594973964269769683465193773476191/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-58031368396358380223817864498825000000000000)
      constant := (1699840620052506031373270592778601026468862080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree151.table
  base := (6706321585840349378577874004331256427347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-118427308051020130049840742013050000000000000)
      constant := (3538536100240947979342362335748675996612549245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (598999550384651786537/100000000000000000000)
  centralHi := (299499775192325893269/50000000000000000000)
  directionLo := (600992898823900492677/100000000000000000000)
  directionHi := (300496449411950246339/50000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree152.table
  base := (7037430994435868870890834179605515285373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-116853537114202324453671180370350000000000000)
      constant := (3447243126432680706625449025169149908762091955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree152.table
  base := (7037424764931212125284937996317288177501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-119233767784812338887678875591150000000000000)
      constant := (3587969649798955387585738478964195444249466835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (600992898823900492677/100000000000000000000)
  centralHi := (300496449411950246339/50000000000000000000)
  directionLo := (602979657627432066719/100000000000000000000)
  directionHi := (3768622860171450417/625000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree153.table
  base := (7372217894639074553718740838078727790401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (2156)
      previous := (1414)
      next := (0)
      square := (19574265383306039753352756750000000000000)
      linear := (-2306751714425252714896208465550000000000000)
      constant := (68532043192176867711153796205136691862184085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree153.table
  base := (1843053031617379881755096373970425403197/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 425000000000000000000000000000000000000000
      center := (1064)
      previous := (721)
      next := (0)
      square := (9787132691653019876676378375000000000000)
      linear := (-1176864975672593605152127540875000000000000)
      constant := (35664165850672359744502357064714972318543490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (602979657627432066719/100000000000000000000)
  centralHi := (3768622860171450417/625000000000000000)
  directionLo := (604959891718645504881/100000000000000000000)
  directionHi := (302479945859322752441/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree154.table
  base := (7710688986048835033144186805576957100641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (109956)
      previous := (72114)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-118435137757173452465742083115750000000000000)
      constant := (3543354469089103124620624130810956109031278735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree154.table
  base := (3855341822620358528981729890352630664733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-60423343626198378281677571373675000000000000)
      constant := (1843930950520259402266717590133808653931617555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (604959891718645504881/100000000000000000000)
  centralHi := (302479945859322752441/50000000000000000000)
  directionLo := (606933664961810628083/100000000000000000000)
  directionHi := (151733416240452657021/25000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree155.table
  base := (4026422121073760898575809372415709517531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-59612969039329508235888767244225000000000000)
      constant := (1795951962590987700540601587249522100758496885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree155.table
  base := (402641964860675083769969025023014288707/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-60826573493094482700596638162725000000000000)
      constant := (1869160301255297010339077092572797669415448450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (606933664961810628083/100000000000000000000)
  centralHi := (151733416240452657021/25000000000000000000)
  directionLo := (30445052009305038057/5000000000000000000)
  directionHi := (608901040186100761141/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree156.table
  base := (419934181884874279083457212889608947571/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-20002789733357430079635497643525000000000000)
      constant := (606797095161705312181804847330114849292400950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree156.table
  base := (419933952972791834894564745770775524711/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-20409934453330195706505234983925000000000000)
      constant := (631520170179899327226561446434687706332073950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30445052009305038057/5000000000000000000)
  centralHi := (608901040186100761141/100000000000000000000)
  directionLo := (122172415841785758477/20000000000000000000)
  directionHi := (305431039604464396193/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree157.table
  base := (2187051787162660389610343521121642599399/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-60403769360815072241924218616925000000000000)
      constant := (1844995203174812046459507373406954641336789330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree157.table
  base := (2187050727514393628391487251858611518081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-61633033226886691538434771740825000000000000)
      constant := (1920131578325972071339804052243294161861762270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122172415841785758477/20000000000000000000)
  centralHi := (305431039604464396193/50000000000000000000)
  directionLo := (612816842858611135581/100000000000000000000)
  directionHi := (306408421429305567791/50000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree158.table
  base := (4550707376032530420684000755210862277947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-60799169521557854244941944303275000000000000)
      constant := (1869763715610349399422257666695689087974900245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree158.table
  base := (4550705414029576139627426194917873489051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-62036263093782795957353838529875000000000000)
      constant := (1945873504568689426856868528477358981575036085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (612816842858611135581/100000000000000000000)
  centralHi := (306408421429305567791/50000000000000000000)
  directionLo := (307382695498191551143/50000000000000000000)
  directionHi := (614765390996383102287/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree159.table
  base := (1182288303253501375152815002153967077713/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-20398189894100212082653223329875000000000000)
      constant := (631565607581410715964438989659329929709181140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree159.table
  base := (9458302793385869611382731728055074768521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-41626328640452600250848603545950000000000000)
      constant := (1314524192816225423432985575369059583040512845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307382695498191551143/50000000000000000000)
  centralHi := (614765390996383102287/100000000000000000000)
  directionLo := (616707782537788227227/100000000000000000000)
  directionHi := (154176945634447056807/25000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree160.table
  base := (490944107479246658418103638415202451897/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-61589969843043418250977395675975000000000000)
      constant := (1919794524531041285522734388060499026289734950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree160.table
  base := (1963775757357459495592228187378111878167/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-125685445655150009590383944215950000000000000)
      constant := (3995739864502385782581597198164620574959269725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (616707782537788227227/100000000000000000000)
  centralHi := (154176945634447056807/25000000000000000000)
  directionLo := (77330509434182896141/12500000000000000000)
  directionHi := (618644075473463169129/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree161.table
  base := (5091570951336942268193820842644984659193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-61985370003786200253995121362325000000000000)
      constant := (1945056820927292551277640052258396008497601655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree161.table
  base := (407325551591256175300173391679103692543/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-126491905388942218428222077794050000000000000)
      constant := (4048248867218387784024392767579422862679347625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77330509434182896141/12500000000000000000)
  centralHi := (618644075473463169129/100000000000000000000)
  directionLo := (620574326889338932319/100000000000000000000)
  directionHi := (3878589543058368327/625000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree162.table
  base := (10551085666065012958609195730979584461679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-41587180109685988171341898032450000000000000)
      constant := (1313655807927536827086722212865685499547126155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree162.table
  base := (527554139230150988190231108794804764687/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-21216394187122404544343368562025000000000000)
      constant := (683516597753278376707418015559594928849727150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620574326889338932319/100000000000000000000)
  centralHi := (3878589543058368327/625000000000000000)
  directionLo := (622498592986278318199/100000000000000000000)
  directionHi := (3112492964931391591/500000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree163.table
  base := (5461356710652332565088303540484489203939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-62776170325271764260030572735025000000000000)
      constant := (1996075197383081060041801537121500260699075565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree163.table
  base := (436908430166251423011201807690784349957/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-128104824856526636103898344950250000000000000)
      constant := (4154292022332122666610010388018268753926589875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (622498592986278318199/100000000000000000000)
  centralHi := (3112492964931391591/500000000000000000)
  directionLo := (78052116137396089753/12500000000000000000)
  directionHi := (24976677163966748721/4000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree164.table
  base := (1412253143832970228146029094352514511751/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-63171570486014546263048298421375000000000000)
      constant := (2021831277364192230290609544567212601633762340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree164.table
  base := (11298022681970775487320769540444946318213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-128911284590318844941736478528350000000000000)
      constant := (4207826174584345704982041019868188842289453355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78052116137396089753/12500000000000000000)
  centralHi := (24976677163966748721/4000000000000000000)
  directionLo := (19572793428609018671/3125000000000000000)
  directionHi := (626329389715488597473/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree165.table
  base := (91226725289766430014809237257738271073/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18326)
      previous := (12019)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-21188990215585776088688674702575000000000000)
      constant := (682583983932559369290949179576445635308831040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree165.table
  base := (2919254638040246822303901297800785768433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (18088)
      previous := (12257)
      next := (0)
      square := (166381255758101337903498432375000000000000)
      linear := (-21619624054018508963262435351075000000000000)
      constant := (710283673867912620546194496688444270870771370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19572793428609018671/3125000000000000000)
  centralHi := (626329389715488597473/100000000000000000000)
  directionLo := (39264751780835331079/6250000000000000000)
  directionHi := (125647205698673059453/20000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree166.table
  base := (301492511604107322848810753748336720061/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-63962370807500110269083749794075000000000000)
      constant := (2073837220647949652248080025243710793629288700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree166.table
  base := (602984917469446902465929269165149254023/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-65262102028951631308706372842275000000000000)
      constant := (2157959814067511282743351501447859220161897050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39264751780835331079/6250000000000000000)
  centralHi := (125647205698673059453/20000000000000000000)
  directionLo := (39383556142446317551/6250000000000000000)
  directionHi := (630136898279141080817/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree167.table
  base := (6223032008029499532030719254389997611051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-64357770968242892272101475480425000000000000)
      constant := (2100087083880701120488558374886460639643906085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree167.table
  base := (155575775735370170025098428616307186669/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54264)
      previous := (36771)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-65665331895847735727625439631325000000000000)
      constant := (2185239464651359897601339214925697666168404600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39383556142446317551/6250000000000000000)
  centralHi := (630136898279141080817/100000000000000000000)
  directionLo := (39502003195278981121/6250000000000000000)
  directionHi := (632032051124463697937/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree168.table
  base := (12836111477501283891356483663758844979301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36652)
      previous := (24038)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-43168780752657116183412800777850000000000000)
      constant := (1417667694308552280229603509573731530995089945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree168.table
  base := (12836109666139044131576396095090922328541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (36176)
      previous := (24514)
      next := (0)
      square := (332762511516202675806996864750000000000000)
      linear := (-44045707841829226764363004280250000000000000)
      constant := (1475126648882795434424667695781166382764741745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell019.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39502003195278981121/6250000000000000000)
  centralHi := (632032051124463697937/100000000000000000000)
  directionLo := (633921538302917101271/100000000000000000000)
  directionHi := (79240192287864637659/12500000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree169.table
  base := (3307460708434441563570587520751836154519/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (54978)
      previous := (36057)
      next := (0)
      square := (499143767274304013710495297125000000000000)
      linear := (-65148571289728456278136926853125000000000000)
      constant := (2153080593362353598191299764000808419459679730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree169.table
  base := (13229841157424796166503005957088636575777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (108528)
      previous := (73542)
      next := (0)
      square := (998287534548608027420990594250000000000000)
      linear := (-132943583259279889130927146418850000000000000)
      constant := (4480622680111798390601632812475139239555993295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell019.Kernel169
